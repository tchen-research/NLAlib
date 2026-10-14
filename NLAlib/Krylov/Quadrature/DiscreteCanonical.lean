import NLAlib.Krylov.Quadrature.DiscreteMeasure
import NLAlib.Krylov.Quadrature.SpectralMoments
import NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix

/-!
# Canonical Jacobi construction for finite discrete measures

The actual normalized moment polynomials evaluated at distinct atomic nodes
give an orthogonal square matrix. It transforms the diagonal node matrix to the
canonical normalized multiplication matrix and transforms the square-root
weights to the first coordinate. Source: Gautschi (2004), §2.2.3;
operator re-derivations OF20–OF21.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix MeasureTheory Finset
open scoped Matrix
namespace NLAlib
variable {N : ℕ}

/-- The square matrix of the actual canonical normalized moment polynomials
at atomic nodes, with square-root atomic weights. The definition is total;
its orthogonal interpretation requires distinct nodes and positive weights. -/
def discreteOrthogonalPolynomialEvaluationMatrix (t w : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun r j => Real.sqrt (w r) * (orthonormalMomentPolynomial
    (polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
      (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r))))
        j.val).eval (t r)

private theorem polynomialIntegral_diagonal_sqrt_apply_eq_sum
    (t w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ℝ[X]) :
    polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
      (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r))) p =
        ∑ r : Fin N, w r * p.eval (t r) := by
  rw [polynomialIntegral_apply, integral_eval_spectralMeasure, aeval_diagonal]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro r _
  calc
    Real.sqrt (w r)*(p.eval (t r)*Real.sqrt (w r)) = (Real.sqrt (w r))^2*p.eval (t r) := by ring
    _ = _ := by rw [Real.sq_sqrt (hw r)]

private theorem discrete_hankel_posDef (t w : Fin N → ℝ)
    (ht : Function.Injective t) (hw : ∀ i, 0 < w i) :
    (hankelMomentMatrix (polynomialIntegral
      (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
      (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))) N).PosDef := by
  apply (posDef_hankelMomentMatrix_spectralMeasure_iff _ _ _).mpr
  rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- The actual canonical normalized polynomial evaluation matrix has
orthonormal columns for distinct finite nodes and positive weights, including
the empty discrete measure.
Source: OF20, canonical discrete orthogonality.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem hasOrthonormalCols_discreteOrthogonalPolynomialEvaluationMatrix
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ i, 0 < w i) :
    HasOrthonormalCols (discreteOrthogonalPolynomialEvaluationMatrix t w) := by
  let L := polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
    (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
  have hpos := discrete_hankel_posDef t w ht hw
  apply hasOrthonormalCols_iff_conjTranspose_mul_self.mpr
  ext i j
  have horth := functional_orthonormalMomentPolynomial_mul L
    (hankelMomentDet_ne_zero_of_posDef_of_le hpos i.isLt.le)
    (hankelMomentDet_ne_zero_of_posDef_of_le hpos j.isLt.le)
    (orthogonalPolynomialNorm_pos_of_posDef hpos i.isLt)
    (orthogonalPolynomialNorm_pos_of_posDef hpos j.isLt)
  rw [polynomialIntegral_diagonal_sqrt_apply_eq_sum t w (fun i => (hw i).le)] at horth
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    discreteOrthogonalPolynomialEvaluationMatrix, Matrix.one_apply]
  have heq : (∑ r : Fin N, (Real.sqrt (w r)*(orthonormalMomentPolynomial L i.val).eval (t r))*
      (Real.sqrt (w r)*(orthonormalMomentPolynomial L j.val).eval (t r))) =
      ∑ r : Fin N, w r*(orthonormalMomentPolynomial L i.val*orthonormalMomentPolynomial L j.val).eval (t r) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [eval_mul]
    calc
      _ = (Real.sqrt (w r))^2*((orthonormalMomentPolynomial L i.val).eval (t r)*
          (orthonormalMomentPolynomial L j.val).eval (t r)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw r).le]
  rw [heq, horth]
  simp only [Fin.val_inj]

/-- The actual canonical discrete evaluation matrix also has orthonormal rows,
because it is square. Source: OF20, finite discrete dual orthogonality.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem discreteOrthogonalPolynomialEvaluationMatrix_mul_conjTranspose_eq_one
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ i, 0 < w i) :
    discreteOrthogonalPolynomialEvaluationMatrix t w *
      (discreteOrthogonalPolynomialEvaluationMatrix t w)ᴴ = 1 :=
  (hasOrthonormalCols_discreteOrthogonalPolynomialEvaluationMatrix t w ht hw).mul_conjTranspose_self

/-- The actual canonical polynomial evaluation matrix conjugates the diagonal
atomic node matrix to the actual normalized multiplication Jacobi matrix.
Source: OF21, the canonical construction rather than an arbitrary Lanczos frame.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem conjTranspose_discreteOrthogonalPolynomialEvaluationMatrix_mul_diagonal_mul_eq_jacobi
    (t w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (discreteOrthogonalPolynomialEvaluationMatrix t w)ᴴ * diagonal t *
      discreteOrthogonalPolynomialEvaluationMatrix t w =
        orthogonalPolynomialJacobiMatrix (polynomialIntegral
          (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
          (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t)
            (fun r => Real.sqrt (w r)))) N := by
  let L := polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
    (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
  ext i j
  rw [orthogonalPolynomialJacobiMatrix, polynomialIntegral_diagonal_sqrt_apply_eq_sum t w hw]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    star_trivial, discreteOrthogonalPolynomialEvaluationMatrix, eval_mul, eval_X]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = (Real.sqrt (w r))^2*(t r*(orthonormalMomentPolynomial L j.val).eval (t r)*
        (orthonormalMomentPolynomial L i.val).eval (t r)) := by ring
    _ = _ := by rw [Real.sq_sqrt (hw r)]

/-- The actual square-root atomic-weight vector transforms to the first
coordinate scaled by the square-root total mass, in positive dimension.
Source: OF21, positive canonical degree-zero normalization.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem conjTranspose_discreteOrthogonalPolynomialEvaluationMatrix_mulVec_sqrt_eq_single
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ i, 0 < w i) (hN : 0<N) :
    (discreteOrthogonalPolynomialEvaluationMatrix t w)ᴴ *ᵥ (fun r => Real.sqrt (w r)) =
      Pi.single ⟨0, hN⟩ (Real.sqrt (orthogonalPolynomialNorm (polynomialIntegral
        (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
        (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t)
          (fun r => Real.sqrt (w r)))) 0)) := by
  let L := polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
    (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
  let Q := discreteOrthogonalPolynomialEvaluationMatrix t w
  let c := Real.sqrt (orthogonalPolynomialNorm L 0)
  have hc : c ≠ 0 := (Real.sqrt_pos.mpr
    (orthogonalPolynomialNorm_pos_of_posDef (discrete_hankel_posDef t w ht hw) hN)).ne'
  have hvec : (fun r => Real.sqrt (w r)) = c • Q.col ⟨0,hN⟩ := by
    ext r
    simp only [Matrix.col, Matrix.transpose_apply, Q, discreteOrthogonalPolynomialEvaluationMatrix,
      orthonormalMomentPolynomial, monicOrthogonalPolynomial_zero,
      mul_one, eval_C, Pi.smul_apply, smul_eq_mul]
    change Real.sqrt (w r) = c*(Real.sqrt (w r)*c⁻¹)
    field_simp
  have hQ : HasOrthonormalCols Q :=
    hasOrthonormalCols_discreteOrthogonalPolynomialEvaluationMatrix t w ht hw
  change Qᴴ *ᵥ (fun r => Real.sqrt (w r)) = Pi.single ⟨0,hN⟩ c
  rw [hvec]
  ext j
  change Q.col j ⬝ᵥ (c • Q.col ⟨0,hN⟩) = (Pi.single ⟨0,hN⟩ c : Fin N → ℝ) j
  rw [dotProduct_smul, hQ.col_dotProduct_col]
  by_cases hj : j = ⟨0,hN⟩ <;> simp [hj]

/-- Canonical normalized polynomials of the actual finite discrete measure
obey dual orthogonality at the atomic nodes, with the exact reciprocal-weight
normalization. Source: OF21, the row orthogonality of the canonical evaluation
matrix, including empty dimension.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem sum_eval_orthonormalMomentPolynomial_diagonal_sqrt_mul_eq_div_weight
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ i, 0 < w i) (r s : Fin N) :
    let L := polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
      (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
    (∑ j : Fin N, (orthonormalMomentPolynomial L j.val).eval (t r) *
      (orthonormalMomentPolynomial L j.val).eval (t s)) = (if r=s then 1 else 0)/w r := by
  let L := polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
    (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
  have horth := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M r s)
    (discreteOrthogonalPolynomialEvaluationMatrix_mul_conjTranspose_eq_one t w ht hw)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.one_apply, discreteOrthogonalPolynomialEvaluationMatrix] at horth
  have hfactor : (Real.sqrt (w r)*Real.sqrt (w s)) *
      (∑ j : Fin N, (orthonormalMomentPolynomial L j.val).eval (t r)*
        (orthonormalMomentPolynomial L j.val).eval (t s)) = if r=s then 1 else 0 := by
    rw [← horth, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  by_cases hrs : r=s
  · subst s
    rw [← pow_two, Real.sq_sqrt (hw r).le, if_pos rfl] at hfactor
    rw [if_pos rfl]
    apply (eq_div_iff (hw r).ne').mpr
    nlinarith [hfactor]
  · rw [if_neg hrs] at hfactor ⊢
    rw [zero_div]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero (Real.sqrt_pos.mpr (hw r)).ne' (Real.sqrt_pos.mpr (hw s)).ne')

end NLAlib
