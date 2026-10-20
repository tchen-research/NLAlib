import NLAlib.RandomMatrix.Gaussian.Basic.GUECoefficientMatrices
import NLAlib.Matrix.Functions.PolynomialSeries

/-!
# Actual diagonal-Gaussian/GUE finite-dimensional interpolation

Every random matrix is an explicit affine function on one canonical product
of independent standard real Gaussian coordinates. The two coefficient
families are the true diagonal coordinates and the true normalized GUE
coordinates proved in `GUECoefficientMatrices`.

Source: arXiv:2108.06312v2, Section 5.1, equation (5.1).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker

namespace NLAlib

variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]

/-- Independent coordinate labels for the true diagonal-Gaussian and GUE
families. The two summands are disjoint, including coincident colors. -/
abbrev GaussianFreeFiniteCoordinate (ι n : Type*) :=
  (ι × n) ⊕ (ι × GUECoordinate Unit n)

/-- Actual interpolating Hermitian coefficients. Their two variance weights
are q and 1−q on the unit interval. -/
def gaussianFreeFiniteCoefficient (A : ι → Matrix d d ℂ) (q : ℝ) :
    GaussianFreeFiniteCoordinate ι n → Matrix (d × n) (d × n) ℂ
  | .inl ia => Real.sqrt q • (A ia.1⊗ₖ(Matrix.single ia.2 ia.2 1 : Matrix n n ℂ))
  | .inr ik => Real.sqrt (1-q) • (A ik.1⊗ₖgueCoefficientMatrix ik.2)

/-- The actual source finite-N interpolation, including its unbounded mean.
The probability measure is the canonical standard Gaussian product on this
exact independent coordinate type. -/
def gaussianFreeFiniteInterpolation (A₀ : Matrix d d ℂ)
    (A : ι → Matrix d d ℂ) (q : ℝ)
    (x : GaussianFreeFiniteCoordinate ι n → ℝ) : Matrix (d × n) (d × n) ℂ :=
  A₀⊗ₖ(1 : Matrix n n ℂ) + ∑ k, x k • gaussianFreeFiniteCoefficient A q k

omit [Fintype ι] [Fintype n] [Fintype d] [DecidableEq ι] [DecidableEq n]
  [DecidableEq d] in
private theorem sum_smul_smul_kronecker {K : Type*} [Fintype K]
    (U : Matrix d d ℂ) (V : K → Matrix n n ℂ) (x : K → ℝ) (t : ℝ) :
    (∑ k, x k • (t • (U⊗ₖV k))) = t • (U⊗ₖ(∑ k, x k • V k)) := by
  ext ab ce
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.kroneckerMap_apply,
    Complex.real_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype d] [DecidableEq ι] [DecidableEq d] in
/-- The canonical coordinate-series realization is literally the source
diagonal-Gaussian/GUE interpolation formula. The GUE families use disjoint
coordinate blocks for different coefficient indices. -/
theorem gaussianFreeFiniteInterpolation_eq_diagonal_add_gue
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (q : ℝ)
    (x : GaussianFreeFiniteCoordinate ι n → ℝ) :
    gaussianFreeFiniteInterpolation A₀ A q x =
      A₀⊗ₖ(1 : Matrix n n ℂ) +
        Real.sqrt q • (∑ i, A i⊗ₖMatrix.diagonal
          (fun a : n => (x (.inl (i,a)) : ℂ))) +
        Real.sqrt (1-q) • (∑ i, A i⊗ₖgueMatrix
          (fun k : GUECoordinate Unit n => x (.inr (i,k))) ()) := by
  have hd (i : ι) :
      (∑ a : n, x (.inl (i,a)) • (Real.sqrt q •
        (A i⊗ₖ(Matrix.single a a 1 : Matrix n n ℂ)))) =
        Real.sqrt q • (A i⊗ₖMatrix.diagonal (fun a : n => (x (.inl (i,a)) : ℂ))) := by
    rw [sum_smul_smul_kronecker]
    congr 2
    simpa only [Matrix.smul_single,Complex.real_smul,smul_eq_mul,mul_one] using
      (Matrix.sum_single_eq_diagonal (fun a : n => (x (.inl (i,a)) : ℂ)))
  have hg (i : ι) :
      (∑ k : GUECoordinate Unit n, x (.inr (i,k)) • (Real.sqrt (1-q) •
        (A i⊗ₖgueCoefficientMatrix k))) =
        Real.sqrt (1-q) • (A i⊗ₖgueMatrix
          (fun k : GUECoordinate Unit n => x (.inr (i,k))) ()) := by
    rw [sum_smul_smul_kronecker]
    congr 2
    rw [gueMatrix_eq_sum_coordinate_smul_coefficient]
    ext a b
    simp only [Matrix.sum_apply,Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  simp only [gaussianFreeFiniteInterpolation,Fintype.sum_sum_type,Fintype.sum_prod_type,
    gaussianFreeFiniteCoefficient,hd,hg,← Finset.smul_sum,add_assoc]

omit [Fintype n] [Fintype d] [DecidableEq n] [DecidableEq d] in
private theorem isHermitian_complex_kronecker {A : Matrix d d ℂ} {B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A⊗ₖB).IsHermitian := by
  rw [Matrix.IsHermitian,Matrix.conjTranspose_kronecker,hA.eq,hB.eq]

omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- Each actual finite-N coefficient is Hermitian, for every real q. -/
theorem gaussianFreeFiniteCoefficient_isHermitian
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    (k : GaussianFreeFiniteCoordinate ι n) :
    (gaussianFreeFiniteCoefficient A q k).IsHermitian := by
  rcases k with ia|ik
  · have he : (Matrix.single ia.2 ia.2 1 : Matrix n n ℂ).IsHermitian := by
      rw [Matrix.IsHermitian,Matrix.conjTranspose_single]
      simp
    exact (isHermitian_complex_kronecker (hA _) he).smul (by rfl)
  · exact (isHermitian_complex_kronecker (hA _) (gueCoefficientMatrix_isHermitian _)).smul
      (by rfl)

omit [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- The actual source interpolant is Hermitian at every sample point,
including empty dimensions and arbitrary Hermitian mean. -/
theorem gaussianFreeFiniteInterpolation_isHermitian
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (q : ℝ)
    (x : GaussianFreeFiniteCoordinate ι n → ℝ) :
    (gaussianFreeFiniteInterpolation A₀ A q x).IsHermitian :=
  (isHermitian_complex_kronecker hA₀ Matrix.isHermitian_one).add
    (isHermitian_sum_smul_real _ (gaussianFreeFiniteCoefficient_isHermitian A hA q) x)

open scoped Matrix.Norms.L2Operator in
/-- The centered actual finite-N interpolation is a true real continuous
linear image of its independent standard Gaussian coordinates. -/
def gaussianFreeFiniteSeriesCLM (A : ι → Matrix d d ℂ) (q : ℝ) :
    (GaussianFreeFiniteCoordinate ι n → ℝ) →L[ℝ] Matrix (d × n) (d × n) ℂ :=
  ∑ k, (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : GaussianFreeFiniteCoordinate ι n => ℝ) k).smulRight
      (gaussianFreeFiniteCoefficient A q k)

omit [Fintype d] [DecidableEq ι] [DecidableEq d] in
open scoped Matrix.Norms.L2Operator in
/-- Evaluation of the true linear map is the actual centered interpolation. -/
@[simp] theorem gaussianFreeFiniteSeriesCLM_apply
    (A : ι → Matrix d d ℂ) (q : ℝ)
    (x : GaussianFreeFiniteCoordinate ι n → ℝ) :
    gaussianFreeFiniteSeriesCLM A q x = ∑ k, x k • gaussianFreeFiniteCoefficient A q k := by
  simp [gaussianFreeFiniteSeriesCLM]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The centered actual source interpolant has a genuine Gaussian matrix
law on the canonical independent coordinate product measure. -/
theorem hasGaussianLaw_gaussianFreeFiniteSeries
    (A : ι → Matrix d d ℂ) (q : ℝ) :
    HasGaussianLaw
      (fun x : GaussianFreeFiniteCoordinate ι n → ℝ =>
        ∑ k, x k • gaussianFreeFiniteCoefficient A q k)
      (gaussianVector (GaussianFreeFiniteCoordinate ι n)) := by
  simpa only [gaussianFreeFiniteSeriesCLM_apply] using
    (hasGaussianLaw_id_gaussianVector (GaussianFreeFiniteCoordinate ι n)).map_fun
      (gaussianFreeFiniteSeriesCLM A q)

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual affine interpolant, with arbitrary fixed mean, has its true
Gaussian matrix law, rather than an assumed moment-matching law. -/
theorem hasGaussianLaw_gaussianFreeFiniteInterpolation
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (q : ℝ) :
    HasGaussianLaw (gaussianFreeFiniteInterpolation (n := n) A₀ A q)
      (gaussianVector (GaussianFreeFiniteCoordinate ι n)) := by
  let μ := (gaussianVector (GaussianFreeFiniteCoordinate ι n)).map
    (gaussianFreeFiniteSeriesCLM (n := n) A q)
  have : IsGaussian μ :=
    ((hasGaussianLaw_id_gaussianVector (GaussianFreeFiniteCoordinate ι n)).map_fun
      (gaussianFreeFiniteSeriesCLM A q)).isGaussian_map
  have he : (gaussianVector (GaussianFreeFiniteCoordinate ι n)).map
      (gaussianFreeFiniteInterpolation A₀ A q) =
      μ.map (fun T => A₀⊗ₖ(1 : Matrix n n ℂ)+T) := by
    dsimp only [μ]
    rw [Measure.map_map (measurable_const_add _) (by fun_prop)]
    congr 1
    funext x
    simp [gaussianFreeFiniteInterpolation]
  refine ⟨?_⟩
  rw [he]
  infer_instance

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual finite-N affine Gaussian matrix has precisely its stated
mean, including singular covariance and empty coordinate families. -/
theorem integral_gaussianFreeFiniteInterpolation
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (q : ℝ) :
    (∫ x : GaussianFreeFiniteCoordinate ι n → ℝ,
      gaussianFreeFiniteInterpolation A₀ A q x
      ∂gaussianVector (GaussianFreeFiniteCoordinate ι n)) =
        A₀⊗ₖ(1 : Matrix n n ℂ) := by
  let μ := gaussianVector (GaussianFreeFiniteCoordinate ι n)
  have hi (k : GaussianFreeFiniteCoordinate ι n) : Integrable (fun x => x k) μ :=
    (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)).integrable one_le_two
  have hz (k : GaussianFreeFiniteCoordinate ι n) : (∫ x, x k ∂μ) = 0 :=
    integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)
  have hsum : Integrable
      (fun x => ∑ k, x k • gaussianFreeFiniteCoefficient (n := n) A q k) μ :=
    integrable_finsetSum _ fun k _ => (hi k).smul_const _
  change (∫ x, A₀⊗ₖ(1 : Matrix n n ℂ)+
    ∑ k, x k • gaussianFreeFiniteCoefficient A q k ∂μ) = _
  rw [integral_add (integrable_const _) hsum,integral_const,
    integral_finsetSum _ (fun k _ => (hi k).smul_const _)]
  simp only [integral_smul_const,hz,zero_smul,Finset.sum_const_zero,
    add_zero,probReal_univ,one_smul]

end NLAlib

end
