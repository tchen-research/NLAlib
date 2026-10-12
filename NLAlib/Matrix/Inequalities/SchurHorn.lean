import NLAlib.Matrix.Inequalities.SchurHornProjection
import NLAlib.Matrix.Inequalities.SchurHornWeights
import NLAlib.Matrix.Inequalities.SchurHornResidual
import NLAlib.Matrix.Inequalities.SchurHornDescent
import NLAlib.Matrix.Inequalities.PlaneRotationDerivative
import NLAlib.Matrix.Inequalities.PlaneRotationCoordinates
/-!
# The real orthogonal Schur–Horn converse

Squared diagonal error attains a minimum on the actual compact orthogonal
group. Rational coordinate rotations make the maximal residual coordinates
reducing. Projected columns of the minimizing orthogonal diagonalizer give the
unit eigenvectors for a decreasing rotation. The resulting scalar threshold
certificate and the lower-subset majorization bound force zero residual.
Source: supplied Schur–Horn variational rederivation; Horn–Johnson (2013),
Theorems 4.3.45 and 4.3.48; Marshall–Olkin–Arnold (2011), 9.B.1–9.B.2.
Atlas: `schur-horn`. All finite real dimensions, signs and multiplicities occur.
-/
noncomputable section
open scoped Matrix BigOperators
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every finite real vector majorized by a prescribed signed spectrum is the
diagonal of a real orthogonal conjugate of that spectrum. Empty dimensions and
repeated eigenvalues need no separate assumptions. Horn–Johnson (2013),
Theorem 4.3.48; supplied variational rederivation.
atlas: schur-horn (partial) -/
theorem exists_orthogonal_diagonal_eq_of_majorized (d lam : n → ℝ)
    (hmajor : Majorized d lam) :
    ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧
      Matrix.diag (Q * Matrix.diagonal lam * Qᵀ) = d := by
  classical
  let F (Q : Matrix n n ℝ) : ℝ := ∑ i, ((Q * Matrix.diagonal lam * Qᵀ) i i - d i) ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨Q, hQ, hmin⟩ := exists_orthogonal_isMinOn_of_continuous F hF
  let A : Matrix n n ℝ := Q * Matrix.diagonal lam * Qᵀ
  have hAt : Aᵀ = A := by simp [A, Matrix.transpose_mul, Matrix.mul_assoc]
  have hA : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hAt
  have hminA : ∀ R : Matrix n n ℝ, Rᵀ * R = 1 →
      (∑ i, (A i i - d i) ^ 2) ≤ ∑ i, ((R * A * Rᵀ) i i - d i) ^ 2 := by
    intro R hR
    have hRQ : HasOrthonormalCols (R * Q) := by
      unfold HasOrthonormalCols
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ R Q, hR,
        Matrix.one_mul]
      exact hQ
    have hbound := hmin (R * Q) hRQ
    simpa only [F, A, Matrix.transpose_mul, Matrix.mul_assoc] using hbound
  refine ⟨Q, hQ, ?_⟩
  change Matrix.diag A = d
  by_contra hneq
  let r : n → ℝ := fun i => A i i - d i
  have hnonzero : ∃ i, r i ≠ 0 := by
    by_contra hnot
    apply hneq
    funext i
    have hall : ∀ i, r i = 0 := by simpa only [not_exists, not_not] using hnot
    exact sub_eq_zero.mp (hall i)
  have htrace : (∑ i, A i i) = ∑ i, lam i := by
    change A.trace = _
    dsimp [A]
    rw [Matrix.trace_mul_cycle, hQ, Matrix.one_mul, Matrix.trace_diagonal]
  have hsumr : ∑ i, r i = 0 := by
    simp only [r, Finset.sum_sub_distrib]
    rw [htrace, hmajor.2]
    ring
  obtain ⟨ρ, hρ, S, hSne, hS, hmax⟩ := exists_pos_max_residual r hsumr hnonzero
  have hcross : ∀ i ∈ S, ∀ j ∉ S, A i j = 0 := by
    intro i hi j hj
    have hstat := diagonal_error_stationarity_of_min A hAt d hminA i j
    change (r i - r j) * A i j = 0 at hstat
    have hdiff : r i - r j ≠ 0 := by
      intro heq
      have hjρ : r j = ρ := (sub_eq_zero.mp heq).symm.trans ((hS i).mp hi)
      exact hj ((hS j).mpr hjρ)
    exact (mul_eq_zero.mp hstat).resolve_left hdiff
  have hcomm := coordinateSelector_commute_of_cross_eq_zero hA S hcross
  have hcommC := coordinateSelector_compl_commute S hcomm
  let p : n → ℝ := columnProjectionMass Q S
  have hp0 : ∀ j, 0 ≤ p j := columnProjectionMass_nonneg Q S
  have hp1 : ∀ j, p j ≤ 1 := columnProjectionMass_le_one hQ S
  have hbudget : ∑ j, p j = (S.card : ℝ) := sum_columnProjectionMass_eq_card hQ S
  have horder : ∀ j k, 0 < p j → p k < 1 → lam j ≤ lam k := by
    intro j k hj hk
    let u := normalizedProjectedColumn Q S j
    let v := normalizedProjectedColumn Q Sᶜ k
    have hu : u ⬝ᵥ u = 1 := normalizedProjectedColumn_dotProduct_self Q S j hj
    have hv : v ⬝ᵥ v = 1 := normalizedProjectedColumn_dotProduct_self Q Sᶜ k
      (by rw [columnProjectionMass_compl hQ S k]; exact sub_pos.mpr hk)
    have huv : u ⬝ᵥ v = 0 := normalizedProjectedColumn_dotProduct_compl_eq_zero Q S j k
    have hAu : A *ᵥ u = lam j • u :=
      mulVec_normalizedProjectedColumn_eq_smul hQ lam rfl S hcomm j
    have hAv : A *ᵥ v = lam k • v :=
      mulVec_normalizedProjectedColumn_eq_smul hQ lam rfl Sᶜ hcommC k
    have hdisjoint : ∀ i, u i * v i = 0 :=
      normalizedProjectedColumn_mul_compl_eq_zero Q S j k
    have hsu : ∀ i ∉ S, u i = 0 := fun i hi =>
      normalizedProjectedColumn_apply_eq_zero_of_not_mem Q S j i hi
    have hsv : ∀ i ∈ S, v i = 0 := fun i hi =>
      normalizedProjectedColumn_apply_eq_zero_of_not_mem Q Sᶜ k i (by simpa using hi)
    have hη : 0 < ∑ i, (A i i - d i) * (u i ^ 2 - v i ^ 2) :=
      sum_mul_sub_sq_pos_of_max_support r u v ρ S hS hmax hu hv hsu hsv
    exact eigenvalue_le_of_diagonal_error_min A hAt d u v hu hv huv
      (lam j) (lam k) hAu hAv hdisjoint hη hminA
  have hbottom := sum_mul_le_sum_sub_sumLargest_of_weight_order lam p hp0 hp1 horder
    (Finset.card_le_univ S) hbudget
  have hmajorS := hmajor.sum_sub_sumLargest_le_sum S
  have hweighted : (∑ j, lam j * p j) = ∑ i ∈ S, A i i :=
    sum_mul_columnProjectionMass_eq_sum_diagonal lam rfl S
  have hresidual : (∑ i ∈ S, A i i) = (∑ i ∈ S, d i) + (S.card : ℝ) * ρ := by
    have heq : ∀ i ∈ S, A i i = d i + ρ := by
      intro i hi
      have hr := (hS i).mp hi
      dsimp [r] at hr
      linarith
    rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib, Finset.sum_const]
    simp [nsmul_eq_mul]
  have hmass : 0 < (S.card : ℝ) := by exact_mod_cast hSne.card_pos
  have hpositive : 0 < (S.card : ℝ) * ρ := mul_pos hmass hρ
  rw [hweighted, hresidual] at hbottom
  linarith

/-- Orthogonal-conjugation diagonals use the squared entries of the actual
conjugating matrix as spectral weights. Horn–Johnson (2013), Theorem 4.3.45;
the identity itself holds without orthogonality. -/
theorem diagonal_conjugation_eq_sq_mulVec (Q : Matrix n n ℝ) (lam : n → ℝ) :
    Matrix.diag (Q * Matrix.diagonal lam * Qᵀ) =
      (Matrix.of fun i j => Q i j ^ 2) *ᵥ lam := by
  funext i
  change (Q * Matrix.diagonal lam * Qᵀ) i i = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Ordinary real majorization is exactly attainment as the diagonal of a real
orthogonal conjugate of the prescribed spectrum. Horn–Johnson (2013),
Theorems 4.3.45 and 4.3.48; signed and repeated spectra and dimension zero.
atlas: schur-horn (partial) -/
theorem majorized_iff_exists_orthogonal_diagonal_eq (d lam : n → ℝ) :
    Majorized d lam ↔ ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧
      Matrix.diag (Q * Matrix.diagonal lam * Qᵀ) = d := by
  constructor
  · exact exists_orthogonal_diagonal_eq_of_majorized d lam
  · rintro ⟨Q, hQ, hdiag⟩
    rw [← hdiag, diagonal_conjugation_eq_sq_mulVec]
    exact majorized_mulVec_of_doublyStochastic lam (sq_entries_mem_doublyStochastic hQ)

/-- The complete real Schur–Horn contract: diagonal majorization and every
subset bound, the full real orthogonal converse for every majorized vector and
prescribed spectrum, and Peierls' convex trace inequality. Horn–Johnson (2013),
Theorems 4.3.45 and 4.3.48; Marshall–Olkin–Arnold (2011), 9.B.1–9.B.2.
The converse follows the supplied compact variational rederivation. All finite
real dimensions, negative eigenvalues and repeated eigenvalues are included.
atlas: schur-horn -/
theorem majorized_diagonal_and_orthogonal_converse_and_sum_convex_le_trace_cfc
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    Majorized (Matrix.diag A) hA.eigenvalues ∧
      (∀ S : Finset n, (∑ i ∈ S, A i i) ≤ sumLargest hA.eigenvalues S.card) ∧
      (∀ d lam : n → ℝ, Majorized d lam ↔
        ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧
          Matrix.diag (Q * Matrix.diagonal lam * Qᵀ) = d) ∧
      (∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ →
        (∑ i, φ (A i i)) ≤ (cfc φ A).trace) := by
  refine ⟨majorized_diagonal_eigenvalues hA, ?_,
    majorized_iff_exists_orthogonal_diagonal_eq, ?_⟩
  · exact (weaklyMajorized_iff_sum_le _ _).mp (majorized_diagonal_eigenvalues hA).1
  · intro φ hφ
    exact sum_convex_diagonal_le_trace_cfc hA hφ

end NLAlib
