import NLAlib.Polynomial.OrthogonalPolynomials.MomentBasisData
import NLAlib.Polynomial.OrthogonalPolynomials.SensitivityDegree
import NLAlib.Polynomial.OrthogonalPolynomials.MomentJacobian

/-! # Native fixed-basis moment Jacobians

The source's arbitrary fixed degree-bounded polynomial basis has constructed
dual coordinates and actual moment inputs. The native positive Hankel domain
gives the advertised recurrence output and Jacobian there. Sensitivity rows
are the basis expansion coefficients of actual sensitivity polynomials.
Source: Gautschi (2004), §2.1; operator re-derivations AQ26--AQ31.
-/

noncomputable section
open Polynomial Module
namespace NLAlib
variable {d n : ℕ}

/-- The actual sensitivity matrix of an original functional in a prescribed
fixed polynomial basis, with alpha rows followed by mass and positive-order
beta rows. -/
def polynomialBasisSensitivityMatrix (b : Basis (Fin d) ℝ (degreeLT ℝ d))
    (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin d) ℝ :=
  fun s k => Sum.elim
    (fun i : Fin n => polynomialBasisCoordinate b k
      (orthogonalRecurrenceAlphaSensitivityPolynomial L i.val))
    (fun i : Fin n => if i.val = 0 then polynomialBasisCoordinate b k 1 else
      polynomialBasisCoordinate b k (orthogonalRecurrenceBetaSensitivityPolynomial L i.val)) s

private theorem alphaSensitivity_coordinate_basis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    {j : ℕ} (hj : j < n) :
    orthogonalRecurrenceAlphaSensitivityPolynomial
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) j =
      orthogonalRecurrenceAlphaSensitivityPolynomial L j := by
  have hjprev : j - 1 < n := by omega
  simp only [orthogonalRecurrenceAlphaSensitivityPolynomial,
    orthogonalPolynomialNorm_coordinate_polynomialBasis_eq b L hd hj,
    orthogonalRecurrenceAlpha_coordinate_polynomialBasis_eq b L hd hj,
    orthogonalRecurrenceBeta_coordinate_polynomialBasis_eq b L hd hj,
    monicOrthogonalPolynomial_coordinate_polynomialBasis_eq b L
      ((Nat.mul_le_mul_left 2 hj.le).trans hd),
    monicOrthogonalPolynomial_coordinate_polynomialBasis_eq b L
      ((Nat.mul_le_mul_left 2 hjprev.le).trans hd)]

private theorem betaSensitivity_coordinate_basis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    {j : ℕ} (hj : j < n) :
    orthogonalRecurrenceBetaSensitivityPolynomial
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) j =
      orthogonalRecurrenceBetaSensitivityPolynomial L j := by
  have hjprev : j - 1 < n := by omega
  simp only [orthogonalRecurrenceBetaSensitivityPolynomial,
    orthogonalPolynomialNorm_coordinate_polynomialBasis_eq b L hd hj,
    orthogonalPolynomialNorm_coordinate_polynomialBasis_eq b L hd hjprev,
    orthogonalRecurrenceBeta_coordinate_polynomialBasis_eq b L hd hj,
    monicOrthogonalPolynomial_coordinate_polynomialBasis_eq b L
      ((Nat.mul_le_mul_left 2 hj.le).trans hd),
    monicOrthogonalPolynomial_coordinate_polynomialBasis_eq b L
      ((Nat.mul_le_mul_left 2 hjprev.le).trans hd)]

/-- At the actual fixed-basis modified moment vector, the output is precisely
the original functional's included alphas, mass, and positive-order betas.
No higher moments enter, and mass is separate from the zero beta boundary.
Source: AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem momentRecurrenceMap_polynomialBasisMomentVector_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d) :
    momentRecurrenceMap (polynomialBasisCoordinate b) n
      (WithLp.toLp 2 (polynomialBasisMomentVector b L)) =
      WithLp.toLp 2 (fun s => Sum.elim
        (fun i : Fin n => orthogonalRecurrenceAlpha L i.val)
        (fun i : Fin n => if i.val = 0 then L 1 else orthogonalRecurrenceBeta L i.val) s) := by
  ext s
  cases s with
  | inl i =>
    simp only [momentRecurrenceMap, PiLp.toLp_apply, Sum.elim_inl,
      orthogonalRecurrenceAlpha_coordinate_polynomialBasis_eq b L hd i.isLt]
  | inr i =>
    simp only [momentRecurrenceMap, PiLp.toLp_apply, Sum.elim_inr,
      orthogonalRecurrenceBeta_coordinate_polynomialBasis_eq b L hd i.isLt]
    congr 1
    apply coordinateMomentFunctional_polynomialBasis_eq_of_degree_lt
    apply degree_one_le.trans_lt
    exact_mod_cast (show 0 < d by have := i.isLt; omega)

/-- The Euclidean Jacobian for an arbitrary actual fixed polynomial basis is
the basis-coordinate matrix of the original functional's sensitivity
polynomials on its actual positive finite Hankel domain. Source: AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem euclideanJacobian_momentRecurrenceMap_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    (hL : (hankelMomentMatrix L n).PosDef) :
    euclideanJacobian (momentRecurrenceMap (polynomialBasisCoordinate b) n)
      (WithLp.toLp 2 (polynomialBasisMomentVector b L)) = polynomialBasisSensitivityMatrix b L n := by
  have hM : (hankelMomentMatrix
      (coordinateMomentFunctional (polynomialBasisCoordinate b)
        (WithLp.toLp 2 (polynomialBasisMomentVector b L)).ofLp) n).PosDef := by
    simpa only [WithLp.ofLp_toLp, hankelMomentMatrix_coordinate_polynomialBasis_eq b L hd] using hL
  rw [euclideanJacobian_momentRecurrenceMap_eq _ hM]
  ext s k
  cases s with
  | inl i =>
    simp only [momentSensitivityMatrix, polynomialBasisSensitivityMatrix,
      Sum.elim_inl, alphaSensitivity_coordinate_basis_eq b L hd i.isLt]
  | inr i =>
    simp only [momentSensitivityMatrix, polynomialBasisSensitivityMatrix,
      Sum.elim_inr, betaSensitivity_coordinate_basis_eq b L hd i.isLt]

/-- Alpha sensitivity coordinates are exactly the coefficients in the actual
fixed basis's bounded-degree representation, including the highest alpha
row. Source: AQ29--AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem polynomialBasisCoordinate_alphaSensitivity_eq_repr
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    (i : Fin n) (k : Fin d) :
    polynomialBasisCoordinate b k (orthogonalRecurrenceAlphaSensitivityPolynomial L i.val) =
      b.repr ⟨orthogonalRecurrenceAlphaSensitivityPolynomial L i.val,
        mem_degreeLT.mpr ((degree_orthogonalRecurrenceAlphaSensitivityPolynomial_le L i.val).trans_lt
          (by exact_mod_cast (show 2*i.val+1 < d by have := i.isLt; omega)))⟩ k := by
  apply polynomialBasisCoordinate_apply_of_degree_lt
  exact (degree_orthogonalRecurrenceAlphaSensitivityPolynomial_le L i.val).trans_lt
    (by exact_mod_cast (show 2*i.val+1 < d by have := i.isLt; omega))

/-- Positive-order beta sensitivity coordinates are the coefficients in the
actual fixed polynomial basis's bounded-degree representation. Source: AQ28--AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem polynomialBasisCoordinate_betaSensitivity_eq_repr
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    (i : Fin n) (k : Fin d) :
    polynomialBasisCoordinate b k (orthogonalRecurrenceBetaSensitivityPolynomial L i.val) =
      b.repr ⟨orthogonalRecurrenceBetaSensitivityPolynomial L i.val,
        mem_degreeLT.mpr ((degree_orthogonalRecurrenceBetaSensitivityPolynomial_le L i.val).trans_lt
          (by exact_mod_cast (show 2*i.val < d by have := i.isLt; omega)))⟩ k := by
  apply polynomialBasisCoordinate_apply_of_degree_lt
  exact (degree_orthogonalRecurrenceBetaSensitivityPolynomial_le L i.val).trans_lt
    (by exact_mod_cast (show 2*i.val < d by have := i.isLt; omega))

/-- A nonempty positive finite moment system has nonzero recurrence-map
output, since the separate mass slot is strictly positive. Thus its normwise
relative normalization has a strictly positive output denominator.
Source: AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem momentRecurrenceMap_ne_zero_of_posDef {c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)}
    {m : EuclideanSpace ℝ (Fin d)} (hn : 0 < n)
    (hM : (hankelMomentMatrix (coordinateMomentFunctional c m.ofLp) n).PosDef) :
    momentRecurrenceMap c n m ≠ 0 := by
  have hmass : 0 < coordinateMomentFunctional c m.ofLp 1 := by
    simpa only [orthogonalPolynomialNorm, monicOrthogonalPolynomial_zero, one_pow] using
      orthogonalPolynomialNorm_pos_of_posDef hM hn
  intro hz
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin n ⊕ Fin n) => v (Sum.inr ⟨0, hn⟩)) hz
  simp only [momentRecurrenceMap, PiLp.toLp_apply, Sum.elim_inr, ite_true,
    PiLp.zero_apply] at h
  exact hmass.ne' h

/-- The input vector of a nonempty positive finite moment system is nonzero;
zero coordinates would give zero mass. Together with the mass-output lemma,
this justifies both normwise relative normalization factors. Source: AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem momentCoordinates_ne_zero_of_posDef {c : Fin d → (ℝ[X] →ₗ[ℝ] ℝ)}
    {m : EuclideanSpace ℝ (Fin d)} (hn : 0 < n)
    (hM : (hankelMomentMatrix (coordinateMomentFunctional c m.ofLp) n).PosDef) : m ≠ 0 := by
  have hmass : 0 < coordinateMomentFunctional c m.ofLp 1 := by
    simpa only [orthogonalPolynomialNorm, monicOrthogonalPolynomial_zero, one_pow] using
      orthogonalPolynomialNorm_pos_of_posDef hM hn
  intro hm
  simp only [coordinateMomentFunctional_apply, hm, WithLp.ofLp_zero, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero] at hmass
  exact (lt_irrefl 0) hmass

/-- The absolute local condition number in the actual fixed modified moments
is the spectral norm of the original functional's sensitivity matrix.
Source: AQ31 and Gautschi (2004), Definition 2.3.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem mapAbsCondition_momentRecurrenceMap_polynomialBasis_eq_specNorm
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    (hL : (hankelMomentMatrix L n).PosDef) :
    mapAbsCondition (momentRecurrenceMap (polynomialBasisCoordinate b) n)
      (WithLp.toLp 2 (polynomialBasisMomentVector b L)) = specNorm (polynomialBasisSensitivityMatrix b L n) := by
  have hM : (hankelMomentMatrix
      (coordinateMomentFunctional (polynomialBasisCoordinate b)
        (WithLp.toLp 2 (polynomialBasisMomentVector b L)).ofLp) n).PosDef := by
    simpa only [WithLp.ofLp_toLp, hankelMomentMatrix_coordinate_polynomialBasis_eq b L hd] using hL
  rw [← specNorm_euclideanJacobian
    ((contDiffAt_momentRecurrenceMap _ hM).differentiableAt (by norm_num)),
    euclideanJacobian_momentRecurrenceMap_polynomialBasis_eq b L hd hL]

/-- The normwise relative condition number in actual fixed-basis moments has
the advertised input norm divided by the original recurrence output norm.
For nonempty positive systems both norms are positive by the preceding
nonvanishing lemmas. Source: AQ31 and Gautschi (2004), Definition 2.4.
atlas: recurrence-coefficient-moment-sensitivity (partial) -/
theorem mapNormRelativeCondition_momentRecurrenceMap_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    (hL : (hankelMomentMatrix L n).PosDef) :
    mapNormRelativeCondition (momentRecurrenceMap (polynomialBasisCoordinate b) n)
      (WithLp.toLp 2 (polynomialBasisMomentVector b L)) =
      specNorm (polynomialBasisSensitivityMatrix b L n) *
        ‖WithLp.toLp 2 (polynomialBasisMomentVector b L)‖ /
        ‖WithLp.toLp 2 (fun s => Sum.elim
          (fun i : Fin n => orthogonalRecurrenceAlpha L i.val)
          (fun i : Fin n => if i.val = 0 then L 1 else orthogonalRecurrenceBeta L i.val) s)‖ := by
  rw [mapNormRelativeCondition,
    mapAbsCondition_momentRecurrenceMap_polynomialBasis_eq_specNorm b L hd hL,
    momentRecurrenceMap_polynomialBasisMomentVector_eq b L hd]

end NLAlib
