import NLAlib

/-! These examples use ordinary downstream Lean options and the default import. They check
that common interfaces compose without access to private helpers or experimental modules. -/

open MeasureTheory ProbabilityTheory NLAlib

noncomputable section

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
