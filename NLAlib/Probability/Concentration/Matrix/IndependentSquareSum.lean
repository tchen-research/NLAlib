import NLAlib.Probability.Concentration.Matrix.MatrixChernoff
import NLAlib.Probability.Concentration.Basic.MatrixCalculus
import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Matrix.Spectral.SpectralBounds
import NLAlib.Matrix.Norms.Reindex

/-!
# Expected spectral norm of independent Hermitian squares

The actual squared increments are positive semidefinite, so the matrix
Chernoff expectation bound applies directly. This supplies the second-moment
estimate used by the matrix resolvent universality argument.

Source: Brailovskaya and van Handel, *Universality and sharp matrix concentration
inequalities*, arXiv:2201.05142v3, Section 6.4, Lemma 6.12. The explicit
coefficient `exp 1 - 1` follows from Tropp's Chernoff bound at parameter one.
The statement also includes empty matrix dimensions, empty increment families,
and a zero increment bound.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- Independent measurable Hermitian increments bounded by `R` have an integrable
sum-of-squares spectral norm, with expectation at most
`(exp 1 - 1) * specNorm (sum E[Z_i^2]) + R^2 * log (card n)`.

This is an explicit-constant form of Brailovskaya--van Handel,
arXiv:2201.05142v3, Section 6.4, Lemma 6.12. It is obtained directly from the
positive-semidefinite Chernoff bound and does not require centered increments.
All integrability follows from the displayed bound; finite empty dimensions
and `R = 0` are allowed.
atlas: matrix-resolvent-gaussian-universality (partial)
-/
theorem integrable_and_integral_specNorm_sum_sq_le_chernoff
    {Ω ι n : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype n] [DecidableEq n]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ι → Ω → Matrix n n ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hMeas : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ) (hHerm : ∀ i, ∀ᵐ ω ∂μ, (Z i ω).IsHermitian)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, specNorm (Z i ω) ≤ R) :
    Integrable (fun ω => specNorm (∑ i, Z i ω ^ 2)) μ ∧
      (∫ ω, specNorm (∑ i, Z i ω ^ 2) ∂μ) ≤
        (Real.exp 1 - 1) * specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) +
          R ^ 2 * Real.log (Fintype.card n) := by
  classical
  have hSqMeas : Measurable (fun A : Matrix n n ℂ => A ^ 2) := by
    simpa only [pow_two, id_eq] using
      (measurable_id.matrix_mul measurable_id :
        Measurable (fun A : Matrix n n ℂ => A * A))
  have hSqPSD : ∀ i, ∀ᵐ ω ∂μ, (Z i ω ^ 2).PosSemidef := by
    intro i
    filter_upwards [hHerm i] with ω hω
    simpa only [hω.eq, pow_two] using Matrix.posSemidef_conjTranspose_mul_self (Z i ω)
  have hSqBound : ∀ i, ∀ᵐ ω ∂μ, specNorm (Z i ω ^ 2) ≤ R ^ 2 := by
    intro i
    filter_upwards [hHerm i, hBound i] with ω hω hb
    have hs : specNorm (Z i ω) ^ 2 = specNorm (Z i ω ^ 2) := by
      simpa only [hω.eq, pow_two] using specNorm_sq_eq_specNorm_conjTranspose_mul_self (Z i ω)
    rw [← hs]
    exact (sq_le_sq₀ (specNorm_nonneg _) hR).mpr hb
  have hSqInt : ∀ i, Integrable (fun ω => Z i ω ^ 2) μ := by
    intro i
    refine Integrable.of_bound (hSqMeas.comp (hMeas i)).aestronglyMeasurable (R ^ 2) ?_
    simpa only [specNorm_eq_norm] using hSqBound i
  have hSumInt : Integrable (fun ω => specNorm (∑ i, Z i ω ^ 2)) μ := by
    simpa only [specNorm_eq_norm] using
      (integrable_finsetSum Finset.univ (fun i _ => hSqInt i)).norm
  refine ⟨hSumInt, ?_⟩
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    have hnorm : ∀ A : Matrix n n ℂ, specNorm A = 0 := by
      intro A
      rw [Subsingleton.elim A 0, specNorm_zero]
    simp only [hnorm, integral_zero, mul_zero, Fintype.card_eq_zero,
      Nat.cast_zero, Real.log_zero, add_zero, le_refl]
  | inr hn =>
    let := hn
    let : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
    let e := Fintype.equivFin n
    let f := (Fintype.equivFin ι).symm
    let E : Matrix n n ℂ ≃ₗ[ℝ] Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
      Matrix.reindexLinearEquiv ℝ ℂ e e
    let Y : Fin (Fintype.card ι) → Ω →
        Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
      fun k ω => E (Z (f k) ω ^ 2)
    have hEMeas : Measurable E := E.toContinuousLinearEquiv.continuous.measurable
    have hYMeas : ∀ k, Measurable (Y k) := by
      intro k
      exact hEMeas.comp (hSqMeas.comp (hMeas (f k)))
    have hYIndep : iIndepFun Y μ := by
      exact (iIndepFun.precomp f.injective hIndep).comp
        (fun _ A => E (A ^ 2)) (fun _ => hEMeas.comp hSqMeas)
    have hYPSD : ∀ k, ∀ᵐ ω ∂μ, (Y k ω).PosSemidef := by
      intro k
      exact (hSqPSD (f k)).mono (fun ω hω => hω.submatrix e.symm)
    have hYBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (Y k ω) ≤ R ^ 2 := by
      intro k
      filter_upwards [hYPSD k, hSqBound (f k)] with ω hω hb
      rw [hω.lambdaMax_eq_specNorm]
      change specNorm ((Z (f k) ω ^ 2).reindex e e) ≤ R ^ 2
      rwa [specNorm_reindex]
    have hSumPSD : ∀ᵐ ω ∂μ, (∑ i, Z i ω ^ 2).PosSemidef := by
      filter_upwards [ae_all_iff.mpr hSqPSD] with ω hω
      exact Matrix.posSemidef_sum _ (fun i _ => hω i)
    have hMeanPSD : (∑ i, ∫ ω, Z i ω ^ 2 ∂μ).PosSemidef := by
      apply Matrix.posSemidef_sum
      intro i _
      rw [← Matrix.nonneg_iff_posSemidef]
      exact integral_nonneg_of_ae ((hSqPSD i).mono (fun ω hω => hω.nonneg))
    have hYsum (ω : Ω) : (∑ k, Y k ω) = E (∑ i, Z i ω ^ 2) := by
      change (∑ k, E (Z (f k) ω ^ 2)) = _
      rw [← map_sum]
      exact congrArg E (f.sum_comp (fun i => Z i ω ^ 2))
    have hYmean : (∑ k, ∫ ω, Y k ω ∂μ) = E (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) := by
      calc
        (∑ k, ∫ ω, Y k ω ∂μ) = ∑ k, E (∫ ω, Z (f k) ω ^ 2 ∂μ) := by
          apply Finset.sum_congr rfl
          intro k _
          exact integral_reindex μ e (fun ω => Z (f k) ω ^ 2)
        _ = E (∑ k, ∫ ω, Z (f k) ω ^ 2 ∂μ) := (map_sum E _ _).symm
        _ = E (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) :=
          congrArg E (f.sum_comp (fun i => ∫ ω, Z i ω ^ 2 ∂μ))
    have hLeft : (∫ ω, lambdaMax (∑ k, Y k ω) ∂μ) =
        ∫ ω, specNorm (∑ i, Z i ω ^ 2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hSumPSD] with ω hω
      rw [hYsum]
      change lambdaMax ((∑ i, Z i ω ^ 2).reindex e e) = _
      have hp : ((∑ i, Z i ω ^ 2).reindex e e).PosSemidef := hω.submatrix e.symm
      rw [hp.lambdaMax_eq_specNorm, specNorm_reindex]
    have hRight : lambdaMax (∑ k, ∫ ω, Y k ω ∂μ) =
        specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) := by
      rw [hYmean]
      change lambdaMax ((∑ i, ∫ ω, Z i ω ^ 2 ∂μ).reindex e e) = _
      have hp : ((∑ i, ∫ ω, Z i ω ^ 2 ∂μ).reindex e e).PosSemidef :=
        hMeanPSD.submatrix e.symm
      rw [hp.lambdaMax_eq_specNorm, specNorm_reindex]
    have hc := integral_lambdaMax_sum_le_chernoff μ Y (sq_nonneg R)
      hYMeas hYIndep hYPSD hYBound (θ := 1) zero_lt_one
    rw [hLeft, hRight] at hc
    simpa only [div_one] using hc

end NLAlib
