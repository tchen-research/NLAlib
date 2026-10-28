import NLAlib.Solvers.Nystrom.ExpectedCondition
import NLAlib.LowRank.RandomizedSVD.Deviation

/-!
# Exact-capture boundaries of Nyström preconditioning

A Gaussian sketch at least as wide as the ambient dimension captures the whole
PSD input. The FTU preconditioned matrix is then a positive scalar identity.
The zero input has the same property at every positive sketch width.
-/

noncomputable section
open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- Gaussian Nyström captures the entire PSD matrix when the sketch width is
at least its ambient dimension, including empty inputs.
atlas: nystrom-pcg (partial) -/
theorem ae_nystrom_eq_of_dim_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n ℓ : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (G : Ω → Matrix (Fin n) (Fin ℓ) ℝ) (hG : HasLaw G (gaussianMatrix (Fin n) (Fin ℓ)) μ)
    (hℓ : n ≤ ℓ) : ∀ᵐ ω ∂μ, nystrom A (G ω) = A := by
  have hr : (CFC.sqrt A).rank ≤ ℓ := (Matrix.rank_le_card_width _).trans (by simpa using hℓ)
  filter_upwards [ae_rsvd_rangeProjector_mul_eq_of_rank_le (CFC.sqrt A) G hG hr] with ω hω
  have hz : specNorm (A - nystrom A (G ω)) = 0 := by
    rw [specNorm_sub_nystrom_eq_sqrt_residual hA, Matrix.sub_mul, Matrix.one_mul,
      hω, sub_self, specNorm_zero, zero_pow (by norm_num)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp (by simpa only [specNorm_eq_norm] using hz))).symm

open scoped Matrix.Norms.L2Operator in
/-- A floor below every eigenvalue leaves only a scaled shifted matrix. -/
theorem nystromPreconditioner_eq_smul_add_of_floor_le_spectrum
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (a μ : ℝ) (hfloor : ∀ t ∈ spectrum ℝ A, a ≤ t) :
    nystromPreconditioner A a μ = (a+μ)⁻¹ • (A + μ • 1) := by
  have hc : cfc (fun t : ℝ => t + μ) A = A + μ • 1 := by
    rw [cfc_add_const μ (fun t : ℝ => t) A (by fun_prop) hA.isHermitian.isSelfAdjoint,
      cfc_id' ℝ A hA.isHermitian.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  rw [← hc, ← cfc_const_mul (a+μ)⁻¹ (fun t : ℝ => t+μ) A (by fun_prop), nystromPreconditioner]
  apply cfc_congr
  intro t ht
  dsimp only
  rw [max_eq_left (hfloor t ht)]
  ring

open scoped Matrix.Norms.L2Operator in
/-- Exact Nyström capture makes the actual symmetrically preconditioned system
a scalar identity whenever the retained floor lies below the spectrum.
atlas: nystrom-pcg (partial) -/
theorem nystromPreconditionedMatrix_self_eq_smul_one
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) (hfloor : ∀ t ∈ spectrum ℝ A, a ≤ t) :
    nystromPreconditionedMatrix A A a μ = (a+μ) • 1 := by
  have hc : a+μ ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos ha hμ)
  have hP := nystromPreconditioner_posDef hA ha hμ
  have he : A + μ • 1 = (a+μ) • nystromPreconditioner A a μ := by
    rw [nystromPreconditioner_eq_smul_add_of_floor_le_spectrum hA a μ hfloor,
      smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [nystromPreconditionedMatrix, he, Matrix.mul_smul, Matrix.smul_mul,
    cfc_inv_sqrt_mul_self_mul_inv_sqrt hP]

open scoped Matrix.Norms.L2Operator in
/-- The ordinary finite condition number of a positive scalar identity is one. -/
theorem conditionNumber_smul_one_toReal {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {c : ℝ} (hc : 0 < c) : (conditionNumber (c • (1 : Matrix n n ℝ))).toReal = 1 := by
  have hp : (c • (1 : Matrix n n ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have hi : (c • (1 : Matrix n n ℝ))⁻¹ = c⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  rw [conditionNumber_toReal_of_isUnit hp.isUnit, hi]
  simp only [specNorm_eq_norm, norm_smul, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_pos hc, abs_of_pos (inv_pos.mpr hc), mul_inv_cancel₀ (ne_of_gt hc)]

open scoped Matrix.Norms.L2Operator in
/-- At width at least the dimension, the retained zero-padded floor lies below
every eigenvalue of a PSD matrix. -/
theorem singularValues_last_le_spectrum {n ℓ : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hℓ : n ≤ ℓ) :
    ∀ t ∈ spectrum ℝ A, singularValues A (ℓ-1) ≤ t := by
  intro t ht
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues, ← hA.isHermitian.range_eigenvalues₀] at ht
  obtain ⟨i,rfl⟩ := ht
  have hi : i.val ≤ ℓ-1 := by have := i.isLt; simp only [Fintype.card_fin] at this; omega
  exact (singularValues_antitone A hi).trans_eq
    (singularValues_eq_eigenvalues₀_of_posSemidef hA i)

open scoped Matrix.Norms.L2Operator in
/-- Full Gaussian capture gives exactly condition one for the native FTU
preconditioned matrix and its actual retained spectral floor.
atlas: nystrom-pcg (partial) -/
theorem ae_conditionNumber_nystromPreconditionedMatrix_eq_one_of_dim_le
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {n ℓ : ℕ} [Nonempty (Fin n)]
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (G : Ω → Matrix (Fin n) (Fin ℓ) ℝ) (hG : HasLaw G (gaussianMatrix (Fin n) (Fin ℓ)) ν)
    (hℓ : n ≤ ℓ) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᵐ ω ∂ν, (conditionNumber
      (nystromPreconditionedMatrix A (nystrom A (G ω)) (nystromFloor A (G ω)) μ)).toReal = 1 := by
  filter_upwards [ae_nystrom_eq_of_dim_le hA G hG hℓ] with ω hω
  rw [nystromFloor, hω, nystromPreconditionedMatrix_self_eq_smul_one hA
    (singularValues_nonneg _ _) hμ (singularValues_last_le_spectrum hA hℓ)]
  exact conditionNumber_smul_one_toReal (add_pos_of_nonneg_of_pos (singularValues_nonneg _ _) hμ)

open scoped Matrix.Norms.L2Operator in
/-- Zero input is captured exactly for every sketch, so its regularized native
FTU system has condition one. This includes the zero effective-dimension case.
atlas: nystrom-pcg (partial) -/
theorem conditionNumber_nystromPreconditionedMatrix_zero_eq_one
    {n ℓ : ℕ} [Nonempty (Fin n)] (G : Matrix (Fin n) (Fin ℓ) ℝ)
    {μ : ℝ} (hμ : 0 < μ) :
    (conditionNumber (nystromPreconditionedMatrix 0 (nystrom 0 G) (nystromFloor 0 G) μ)).toReal = 1 := by
  have hz : nystrom (0 : Matrix (Fin n) (Fin n) ℝ) G = 0 := by simp [nystrom]
  have hf : nystromFloor (0 : Matrix (Fin n) (Fin n) ℝ) G = 0 := by
    rw [nystromFloor, hz]
    exact singularValues_eq_zero_of_rank_le _ (by simp)
  rw [hz, hf, nystromPreconditionedMatrix_self_eq_smul_one Matrix.PosSemidef.zero
    (by norm_num) hμ (fun t ht => spectrum_nonneg_of_nonneg (show (0 : Matrix (Fin n) (Fin n) ℝ) ≤ 0 from le_rfl) ht),
    zero_add]
  exact conditionNumber_smul_one_toReal hμ

end NLAlib
