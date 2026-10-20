import NLAlib

/-! These examples use ordinary downstream Lean options and the default import. They check
that common interfaces compose without access to private helpers or experimental modules. -/

open MeasureTheory ProbabilityTheory NLAlib

noncomputable section

open scoped Matrix

-- Full QR is a unitary factorization over either scalar field, including rectangular inputs.
example {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    {A R : Matrix (Fin m) (Fin n) 𝕜} {Q : Matrix (Fin m) (Fin m) 𝕜}
    (h : IsFullQR A Q R) : Qᴴ * A = R :=
  h.conjTranspose_mul_eq

example {m n : ℕ} {A R : Matrix (Fin m) (Fin n) ℂ}
    {Q : Matrix (Fin m) (Fin m) ℂ} (h : IsFullQR A Q R) (hnm : n ≤ m) :
    IsQR A (Q.submatrix id (Fin.castLE hnm)) (R.submatrix (Fin.castLE hnm) id) :=
  h.isQR_castLE hnm

-- A genuinely complex phase checks that QR uses the adjoint rather than the transpose.
example : IsFullQR (!![Complex.I; 0] : Matrix (Fin 2) (Fin 1) ℂ)
    (!![Complex.I, 0; 0, 1]) (!![1; 0]) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · change (!![Complex.I, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
      !![Complex.I, 0; 0, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

-- Thin QR preserves singular values on arbitrary finite row/column labels over ℂ.
example {m n : Type*} [Fintype m] [Fintype n] [LinearOrder n]
    {A Q : Matrix m n ℂ} {R : Matrix n n ℂ} (h : IsQR A Q R) :
    singularValues R = singularValues A :=
  singularValues_eq_of_qr h.orth h.eq.symm

-- Finite index types need not be `Fin`; complex matrices use the same norm API.
example {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    specNorm (A * B) ≤ specNorm A * specNorm B :=
  specNorm_mul_le A B

-- An orthonormal matrix acts as a native Euclidean linear isometry.
example {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {Q : Matrix m n ℂ} (hQ : HasOrthonormalCols Q) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ m :=
  hQ.toLinearIsometry

-- The arbitrary probability space and a.e. measurability are carried by HasLaw.
example {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    {x : Ω → n → ℝ} (hx : HasLaw x (gaussianVector n) μ) (i : n) :
    HasLaw (fun ω => x ω i) (gaussianReal 0 1) μ :=
  hx.hasLaw_eval_gaussianReal i

-- Native coordinate laws and joint independence construct the vector law.
example {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    {x : n → Ω → ℝ} (hx : ∀ i, HasLaw (x i) (gaussianReal 0 1) μ)
    (hind : iIndepFun x μ) :
    HasLaw (fun ω i => x i ω) (gaussianVector n) μ :=
  hasLaw_gaussianVector_of_iIndepFun hx hind

-- Embedding guarantees compose with a caller's tolerance comparison.
example {k m d : Type*} [Fintype k] [Fintype m] [Fintype d]
    {S : Matrix k m ℝ} {U : Matrix m d ℝ} {ε ε' : ℝ}
    (h : IsSubspaceEmbedding S U ε) (hε : ε ≤ ε') :
    IsSubspaceEmbedding S U ε' :=
  h.mono hε

-- A native PMF supplies the law of a random solver run. At zero steps its
-- expected error is the initial error, including empty matrix dimensions.
example {m n s J : Type*} [Fintype m] [Fintype n] [Fintype s] [Fintype J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (A : Matrix m n ℝ) (b : m → ℝ) (q : PMF J)
    (S : J → Matrix m s ℝ) (xs x : n → ℝ) :
    (∫ ω, ‖WithLp.toLp 2 (SketchProject.run A b S 0 ω x - xs)‖ ^ 2
      ∂SketchProject.iidPathLaw q 0) = ‖WithLp.toLp 2 (x - xs)‖ ^ 2 := by
  rw [SketchProject.integral_sqErr_iidPathLaw]
  simp only [SketchProject.expErr, norm_toLp_sq_eq_dotProduct_self]

-- A compact Hermitian sample law constructs an actual probability law
-- and an attained variational logarithmic potential below its lower edge.
open scoped Matrix.Norms.L2Operator ComplexOrder in
example {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (hα : 0 < α) :
    ∃ μ : FiniteMeasure ℝ, μ.mass = 1 ∧ IsCompact (μ : Measure ℝ).support ∧
      ∀ u < sInf (μ : Measure ℝ).support, ∃ S : Matrix n n ℂ,
        S ∈ matrixKStableDomain ν α ∧
        logarithmicPotential (μ : Measure ℝ) u = matrixKPotential ν α u S / Fintype.card n ∧
        ∀ Q ∈ matrixKStableDomain ν α, matrixKPotential ν α u S ≤ matrixKPotential ν α u Q := by
  obtain ⟨_F, _hFa, _hF, μ, hmass, hcompact, _htrace, hmin⟩ :=
    exists_matrixKTransform_law_variational_logarithmicPotential ν hν α hα
  refine ⟨μ, hmass, hcompact, ?_⟩
  intro u hu
  obtain ⟨S, hS, _hK, hvalue, hminimum, _hdet⟩ := hmin u hu
  exact ⟨S, hS, hvalue, hminimum⟩
