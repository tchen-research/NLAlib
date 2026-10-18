import NLAlib.RandomMatrix.Covariance.SampleCovariance
import NLAlib.Matrix.Functions.Whitening
import NLAlib.ForMathlib.MeasureTheory.MatrixEntriesIntegral
import NLAlib.Matrix.Basic.QuadraticFunctional
import NLAlib.Matrix.Norms.Core
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Probability.Moments.Variance

/-!
# Second and fourth moments under covariance whitening

Finite second vector moments give the actual covariance matrix integral.
Linear transformations carry it by congruence, so inverse-square-root
whitening makes its second moment exactly the identity. Directional fourth
moment bounds are preserved by the same transformation.
Source: Tropp (2026), Theorem 3.3 and Section 3.3.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace NLAlib

variable {Ω d : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d]
  {μ : Measure Ω}

open scoped Matrix.Norms.L2Operator in
/-- Finite second vector moments imply integrability of every entry and of
the actual rank-one covariance matrix. -/
theorem integrable_vecMulVec_self_of_memLp_two {X : Ω → d → ℝ} (hX : MemLp X 2 μ) :
    Integrable (fun ω => vecMulVec (X ω) (X ω)) μ := by
  apply Matrix.integrable_iff_entries.mpr
  intro i j
  exact (hX.eval i).integrable_mul (hX.eval j)

open scoped Matrix.Norms.L2Operator in
/-- Fourth vector moments give square integrability of the rank-one
covariance, as required by full-entry Gaussian proxy matching. -/
theorem memLp_two_vecMulVec_self_of_memLp_four {X : Ω → d → ℝ} (hX : MemLp X 4 μ) :
    MemLp (fun ω => vecMulVec (X ω) (X ω)) 2 μ := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num⟩
  apply Matrix.memLp_iff_entries.mpr
  intro i j
  exact (ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 2 (hX.eval i) (hX.eval j)

open scoped Matrix.Norms.L2Operator in
/-- Applying a deterministic linear map transforms the actual second
moment matrix by congruence. -/
theorem integral_vecMulVec_mulVec_eq_congruence {X : Ω → d → ℝ}
    (hX : MemLp X 2 μ) (S : Matrix d d ℝ) :
    (∫ ω, vecMulVec (S *ᵥ X ω) (S *ᵥ X ω) ∂μ) =
      S * (∫ ω, vecMulVec (X ω) (X ω) ∂μ) * Sᵀ := by
  let L := ContinuousLinearMap.mulLeftRight ℝ (Matrix d d ℝ) S Sᵀ
  have h := L.integral_comp_comm (integrable_vecMulVec_self_of_memLp_two hX)
  have hp (ω : Ω) : vecMulVec (S *ᵥ X ω) (S *ᵥ X ω) =
      S * vecMulVec (X ω) (X ω) * Sᵀ := by
    simpa only [star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.vecMulVec_mulVec_star_mulVec S (X ω)
  simpa only [L, ContinuousLinearMap.mulLeftRight_apply, ← hp] using h

open scoped Matrix.Norms.L2Operator in
/-- Any positive-definite actual second moment admits a concrete invertible
linear whitening map whose transformed second moment is the identity. -/
theorem exists_isUnit_whitening_second_moment {X : Ω → d → ℝ}
    (hX : MemLp X 2 μ) (K : Matrix d d ℝ) (hK : K.PosDef)
    (hsecond : (∫ ω, vecMulVec (X ω) (X ω) ∂μ) = K) :
    ∃ S : Matrix d d ℝ, IsUnit S ∧ S * K * Sᵀ = 1 ∧
      (∫ ω, vecMulVec (S *ᵥ X ω) (S *ᵥ X ω) ∂μ) = 1 := by
  obtain ⟨S, hS, hwhite⟩ := hK.exists_isUnit_whitening
  change S * K * Sᵀ = 1 at hwhite
  refine ⟨S, hS, hwhite, ?_⟩
  rw [integral_vecMulVec_mulVec_eq_congruence hX S, hsecond, hwhite]

omit [DecidableEq d] in
/-- A linear change of variables transports each real linear marginal to
the transpose-transformed test vector. -/
theorem dotProduct_mulVec_eq_dotProduct_transpose (S : Matrix d d ℝ) (x a : d → ℝ) :
    (S *ᵥ x) ⬝ᵥ a = x ⬝ᵥ (Sᵀ *ᵥ a) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]

omit [DecidableEq d] in
/-- Directional fourth-moment variance control is preserved under every
deterministic linear map, hence under invertible whitening. -/
theorem variance_sq_dotProduct_mulVec_le {X : Ω → d → ℝ} {β : ℝ}
    (hfourth : ∀ a : d → ℝ,
      Var[fun ω => (X ω ⬝ᵥ a) ^ 2; μ] ≤
        β ^ 2 * (∫ ω, (X ω ⬝ᵥ a) ^ 2 ∂μ) ^ 2)
    (S : Matrix d d ℝ) (a : d → ℝ) :
    Var[fun ω => ((S *ᵥ X ω) ⬝ᵥ a) ^ 2; μ] ≤
      β ^ 2 * (∫ ω, ((S *ᵥ X ω) ⬝ᵥ a) ^ 2 ∂μ) ^ 2 := by
  simpa only [dotProduct_mulVec_eq_dotProduct_transpose] using hfourth (Sᵀ *ᵥ a)

open scoped Matrix.Norms.L2Operator in
/-- The second moment of a real linear marginal is the quadratic form of
the actual rank-one second-moment matrix. -/
theorem integral_dotProduct_sq_eq_quadForm_second_moment {X : Ω → d → ℝ}
    (hX : MemLp X 2 μ) (a : d → ℝ) :
    (∫ ω, (X ω ⬝ᵥ a) ^ 2 ∂μ) =
      quadForm (∫ ω, vecMulVec (X ω) (X ω) ∂μ) a := by
  have h := (quadFormContinuousLinearMap a).integral_comp_comm
    (integrable_vecMulVec_self_of_memLp_two hX)
  have hpoint (ω : Ω) : quadForm (vecMulVec (X ω) (X ω)) a = (X ω ⬝ᵥ a) ^ 2 := by
    simp only [quadForm, star_trivial, Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul]
    rw [dotProduct_comm a (X ω)]
    ring
  simpa only [quadFormContinuousLinearMap_apply, hpoint] using h

open scoped Matrix.Norms.L2Operator in
/-- Isotropy makes the second moment of every real linear marginal the
squared Euclidean norm of its test vector. -/
theorem integral_dotProduct_sq_eq_norm_sq_of_isotropic {X : Ω → d → ℝ}
    (hX : MemLp X 2 μ)
    (hisotropic : (∫ ω, vecMulVec (X ω) (X ω) ∂μ) = (1 : Matrix d d ℝ))
    (a : d → ℝ) :
    (∫ ω, (X ω ⬝ᵥ a) ^ 2 ∂μ) = ‖WithLp.toLp 2 a‖ ^ 2 := by
  rw [integral_dotProduct_sq_eq_quadForm_second_moment hX a, hisotropic]
  simp only [quadForm, Matrix.one_mulVec, star_trivial, norm_toLp_sq_eq_dotProduct_self]

open scoped Matrix.Norms.L2Operator in
/-- For an isotropic law, directional fourth-moment variance control gives
the dimension-free weak variance bound on every unit rank-one probe. -/
theorem variance_sq_dotProduct_le_of_isotropic {X : Ω → d → ℝ} {β : ℝ}
    (hX : MemLp X 2 μ)
    (hisotropic : (∫ ω, vecMulVec (X ω) (X ω) ∂μ) = (1 : Matrix d d ℝ))
    (hfourth : ∀ a : d → ℝ,
      Var[fun ω => (X ω ⬝ᵥ a) ^ 2; μ] ≤
        β ^ 2 * (∫ ω, (X ω ⬝ᵥ a) ^ 2 ∂μ) ^ 2)
    (a : d → ℝ) (ha : ‖WithLp.toLp 2 a‖ = 1) :
    Var[fun ω => (X ω ⬝ᵥ a) ^ 2; μ] ≤ β ^ 2 := by
  simpa only [integral_dotProduct_sq_eq_norm_sq_of_isotropic hX hisotropic a,
    ha, one_pow, mul_one] using hfourth a

end NLAlib
