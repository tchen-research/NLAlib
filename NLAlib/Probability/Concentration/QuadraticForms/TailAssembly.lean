/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb (Y. Zhang, J. D. Lee, F. Liu; Apache-2.0),
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. The proof is stated in NLAlib's matrix
vocabulary (`quadForm`, `frobSq`, `frobNorm`, `specNorm`); there is no HighDimProb dependency.
-/
import NLAlib.Probability.Concentration.QuadraticForms.Decoupling
import NLAlib.Probability.Concentration.Scalar.ScalarBernstein
/-!
# Hanson–Wright proof: TailAssembly

A focused leaf of the transported independent-coordinate proof.
Its declarations live in namespace `NLAlib` (generic scalar sub-Gaussian facts are in
`NLAlib.Probability.SubGaussian.*`); the public bounds are in `NLAlib.Probability.Concentration.QuadraticForms.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb (Zhang–Lee–Liu, Apache-2.0).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- Hanson-Wright MGF certificate from independent sub-Gaussian coordinates. -/
theorem hasHansonWrightMGF_of_subgaussian {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hC_domain : 4 * exp 1 ≤ C)
    (hC_diag_quad : 8 * exp 1 ^ 3 ≤ C)
    (hC_offdiag_domain : 16 * exp 1 ≤ C ^ 2)
    (hC_offdiag_quad : 64 * exp 1 ^ 2 ≤ C)
    (hOp : 0 < specNorm A)
    (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    HasHansonWrightMGF μ A X K C := by
  let D : Ω → ℝ := diagonalCenteredQuadraticForm μ A X
  let O : Ω → ℝ := fun ω => quadForm (offDiagonalMatrix A) (fun i => X i ω)
  let B : ℝ → ℝ := fun l => C * l ^ 2 * K ^ 4 * frobNorm A ^ 2
  have hX_meas : ∀ i, AEMeasurable (X i) μ := fun i => (hmgf i).aemeasurable
  have hKsq_op_pos : 0 < K ^ 2 * specNorm A := by positivity
  have hCq_pos : 0 < C / 4 := by positivity
  have hCq_domain : exp 1 ≤ C / 4 := by linarith
  have hCq_quad : 2 * exp 1 ^ 3 ≤ C / 4 := by linarith
  have hcenter_eq :
      centeredQuadraticForm μ A X = fun ω => D ω + O ω := by
    dsimp [D, O]
    exact centeredQuadraticForm_eq_diagonal_add_offDiagonal A hind hmgf
  have hD_ae : AEMeasurable D μ := by
    dsimp [D, diagonalCenteredQuadraticForm]
    exact Finset.aemeasurable_fun_sum _ fun i _ =>
      ((((hX_meas i).pow_const 2).sub_const _).const_mul _)
  have hO_ae : AEMeasurable O μ := by
    dsimp [O]
    exact randomQuadraticForm_aemeasurable (offDiagonalMatrix A) hX_meas
  have hmain : ∀ l : ℝ, |l| ≤ (2 * C * K ^ 2 * specNorm A)⁻¹ →
      Integrable (fun ω => exp (l * centeredQuadraticForm μ A X ω)) μ ∧
        ∫ ω, exp (l * centeredQuadraticForm μ A X ω) ∂μ ≤ exp (B l) := by
    intro l hl
    have hden_eq : 2 * C * (K ^ 2 * specNorm A) =
        2 * C * K ^ 2 * specNorm A := by ring
    have hl_a : |l| ≤ (2 * C * (K ^ 2 * specNorm A))⁻¹ := by
      rw [hden_eq]
      exact hl
    have hdiag_domain_a :
        |2 * l| ≤ (2 * (C / 4) * (K ^ 2 * specNorm A))⁻¹ :=
      abs_two_mul_le_inv_quarter_of_abs_le
        (a := K ^ 2 * specNorm A) (C := C) (l := l) hKsq_op_pos hC hl_a
    have hdiag_domain :
        |2 * l| ≤ (2 * (C / 4) * K ^ 2 * specNorm A)⁻¹ := by
      simpa [mul_assoc] using hdiag_domain_a
    have hD_int : Integrable (fun ω => exp ((2 * l) * D ω)) μ := by
      dsimp [D]
      exact diagonalCenteredQuadraticForm_integrable_exp
        (A := A) (X := X) (K := K) (C := C / 4) (θ := 2 * l)
        hK hCq_pos hCq_domain hOp hind hmgf hdiag_domain
    have hD_cgf :
        cgf D μ (2 * l) ≤ B l := by
      have hbase :=
        diagonalCenteredQuadraticForm_cgf_le
          (A := A) (X := X) (K := K) (C := C / 4) (θ := 2 * l)
          hK hCq_pos hCq_domain hCq_quad hOp hind hmgf hdiag_domain
      dsimp [D, B] at hbase ⊢
      calc
        cgf (diagonalCenteredQuadraticForm μ A X) μ (2 * l)
            ≤ (C / 4) * (2 * l) ^ 2 * K ^ 4 * frobNorm A ^ 2 := hbase
        _ = C * l ^ 2 * K ^ 4 * frobNorm A ^ 2 := by ring
    have hD_mgf_le : ∫ ω, exp ((2 * l) * D ω) ∂μ ≤ exp (B l) := by
      change mgf D μ (2 * l) ≤ exp (B l)
      rw [← exp_cgf hD_int]
      exact exp_le_exp.mpr hD_cgf
    have hsmall_offdiag :
        (K ^ 2 * (4 * (2 * l)) ^ 2 / 2) * K ^ 2 *
            specNorm A ^ 2 * exp 1 ≤ 1 / 2 :=
      offDiagonal_small_two_mul_of_abs_le hK hC hOp hC_offdiag_domain hl
    have hO_int : Integrable (fun ω => exp ((2 * l) * O ω)) μ := by
      change Integrable (fun ω => exp ((2 * l) *
        quadForm (offDiagonalMatrix A) (fun i => X i ω))) μ
      exact integrable_exp_quadraticForm_offDiagonal
        (A := A) (X := X) (K := K) (l := 2 * l)
        hind hmgf (lt_of_le_of_lt hsmall_offdiag (by norm_num))
    have hO_mgf_le : ∫ ω, exp ((2 * l) * O ω) ∂μ ≤ exp (B l) := by
      have hbase :=
        integral_exp_quadraticForm_offDiagonal_le
          (A := A) (X := X) (K := K) (l := 2 * l)
          hind hmgf hsmall_offdiag
      have hexp_le :
          exp (exp 1 ^ 2 * (4 * (2 * l)) ^ 2 * K ^ 4 *
              frobNorm A ^ 2) ≤ exp (B l) := by
        apply exp_le_exp.mpr
        dsimp [B]
        exact offDiagonal_exponent_two_mul_le
          (K := K) (C := C) (F := frobNorm A) (l := l) hC_offdiag_quad
      change ∫ ω, exp ((2 * l) *
        quadForm (offDiagonalMatrix A) (fun i => X i ω)) ∂μ ≤ exp (B l)
      exact hbase.trans hexp_le
    let R : Ω → ℝ :=
      fun ω => (exp ((2 * l) * D ω) + exp ((2 * l) * O ω)) / 2
    have hR_int : Integrable R μ := by
      change Integrable
        (fun ω => (exp ((2 * l) * D ω) + exp ((2 * l) * O ω)) / 2) μ
      exact (hD_int.add hO_int).div_const 2
    have hleft_aesm :
        AEStronglyMeasurable (fun ω => exp (l * (D ω + O ω))) μ :=
      (((hD_ae.add hO_ae).const_mul l).exp).aestronglyMeasurable
    have hpoint :
        (fun ω => exp (l * (D ω + O ω))) ≤ᵐ[μ] R := by
      filter_upwards with ω
      dsimp [R]
      have hconv := exp_add_le_average_exp_two (l * D ω) (l * O ω)
      convert hconv using 1 <;> ring_nf
    have hDO_int : Integrable (fun ω => exp (l * (D ω + O ω))) μ := by
      refine Integrable.mono' hR_int hleft_aesm ?_
      filter_upwards [hpoint] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
      exact hω
    have hcenter_int : Integrable (fun ω => exp (l * centeredQuadraticForm μ A X ω)) μ :=
      hDO_int.congr (ae_of_all _ fun ω => by
        change exp (l * (D ω + O ω)) = exp (l * centeredQuadraticForm μ A X ω)
        rw [← congrFun hcenter_eq ω])
    have hDO_integral_le :
        ∫ ω, exp (l * (D ω + O ω)) ∂μ ≤ exp (B l) := by
      have hmono : ∫ ω, exp (l * (D ω + O ω)) ∂μ ≤ ∫ ω, R ω ∂μ :=
        integral_mono_ae hDO_int hR_int hpoint
      have hR_integral :
          ∫ ω, R ω ∂μ =
            (∫ ω, exp ((2 * l) * D ω) ∂μ +
              ∫ ω, exp ((2 * l) * O ω) ∂μ) / 2 := by
        change (∫ ω, (exp ((2 * l) * D ω) + exp ((2 * l) * O ω)) / 2 ∂μ) = _
        rw [integral_div]
        rw [integral_add hD_int hO_int]
      have hsum_le :
          ∫ ω, exp ((2 * l) * D ω) ∂μ +
              ∫ ω, exp ((2 * l) * O ω) ∂μ ≤
            exp (B l) + exp (B l) :=
        add_le_add hD_mgf_le hO_mgf_le
      calc
        ∫ ω, exp (l * (D ω + O ω)) ∂μ ≤ ∫ ω, R ω ∂μ := hmono
        _ = (∫ ω, exp ((2 * l) * D ω) ∂μ +
              ∫ ω, exp ((2 * l) * O ω) ∂μ) / 2 := hR_integral
        _ ≤ (exp (B l) + exp (B l)) / 2 :=
          div_le_div_of_nonneg_right hsum_le (by norm_num)
        _ = exp (B l) := by ring
    have hcenter_integral_le :
        ∫ ω, exp (l * centeredQuadraticForm μ A X ω) ∂μ ≤ exp (B l) := by
      calc
        ∫ ω, exp (l * centeredQuadraticForm μ A X ω) ∂μ
            = ∫ ω, exp (l * (D ω + O ω)) ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              rw [congrFun hcenter_eq ω]
        _ ≤ exp (B l) := hDO_integral_le
    exact ⟨hcenter_int, hcenter_integral_le⟩
  refine ⟨?_, ?_⟩
  · intro l hl
    have hres := hmain l hl
    have hmgf_pos : 0 < mgf (centeredQuadraticForm μ A X) μ l := mgf_pos hres.1
    have hmgf_le : mgf (centeredQuadraticForm μ A X) μ l ≤ exp (B l) := by
      exact hres.2
    calc
      cgf (centeredQuadraticForm μ A X) μ l
          = log (mgf (centeredQuadraticForm μ A X) μ l) := rfl
      _ ≤ log (exp (B l)) := log_le_log hmgf_pos hmgf_le
      _ = C * l ^ 2 * K ^ 4 * frobNorm A ^ 2 := by
        dsimp [B]
        rw [log_exp]
  · intro l hl
    exact (hmain l hl).1

open scoped Matrix.Norms.L2Operator in
/-- A proved Hanson-Wright MGF certificate for bounded coordinates.

If each coordinate satisfies `|Xᵢ| ≤ K` almost surely, then the quadratic form lies
in the interval `[-K²‖A‖₁, K²‖A‖₁]`.  The centered quadratic form is therefore
bounded by `2K²‖A‖₁`; the local bounded MGF lemma above gives a quadratic CGF
estimate.  The explicit side condition compares this bounded-coordinate constant
with the Frobenius-scale constant used by the Hanson-Wright tail statement. -/
theorem hasHansonWrightMGF_of_bounded {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Ω → ℝ}
    {K C : ℝ} (hK : 0 ≤ K) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (hX_bound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hC_bound : 2 * entrywiseL1Norm A ^ 2 ≤ C * frobNorm A ^ 2) :
    HasHansonWrightMGF μ A X K C := by
  set B : ℝ := K ^ 2 * entrywiseL1Norm A with hB_def
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]
    exact mul_nonneg (sq_nonneg K) (entrywiseL1Norm_nonneg A)
  have hZ_meas : AEMeasurable (randomQuadraticForm A X) μ :=
    randomQuadraticForm_aemeasurable A hX_meas
  have hZ_range :
      ∀ᵐ ω ∂μ, randomQuadraticForm A X ω ∈ Set.Icc (-B) B := by
    simpa [B, hB_def] using
      randomQuadraticForm_mem_Icc_of_ae_coord_bound (μ := μ) A hK hX_bound
  have hZ_int : Integrable (randomQuadraticForm A X) μ :=
    Integrable.of_mem_Icc (-B) B hZ_meas hZ_range
  have hmean_abs : |∫ ω, randomQuadraticForm A X ω ∂μ| ≤ B := by
    have hlower :
        -B ≤ ∫ ω, randomQuadraticForm A X ω ∂μ := by
      calc -B = ∫ _ω, (-B : ℝ) ∂μ := by simp
        _ ≤ ∫ ω, randomQuadraticForm A X ω ∂μ := by
            exact integral_mono_ae (integrable_const _) hZ_int
              (hZ_range.mono fun _ hω => hω.1)
    have hupper :
        ∫ ω, randomQuadraticForm A X ω ∂μ ≤ B := by
      calc ∫ ω, randomQuadraticForm A X ω ∂μ
          ≤ ∫ _ω, (B : ℝ) ∂μ := by
            exact integral_mono_ae hZ_int (integrable_const _)
              (hZ_range.mono fun _ hω => hω.2)
        _ = B := by simp
    exact abs_le.mpr ⟨hlower, hupper⟩
  have hY_meas : AEMeasurable (centeredQuadraticForm μ A X) μ :=
    hZ_meas.sub_const _
  have hY_bound :
      ∀ᵐ ω ∂μ, |centeredQuadraticForm μ A X ω| ≤ 2 * B := by
    filter_upwards [hZ_range] with ω hω
    have hZ_abs : |randomQuadraticForm A X ω| ≤ B := abs_le.mpr hω
    unfold centeredQuadraticForm
    calc |randomQuadraticForm A X ω - ∫ x, randomQuadraticForm A X x ∂μ|
        ≤ |randomQuadraticForm A X ω| + |∫ x, randomQuadraticForm A X x ∂μ| :=
          abs_sub _ _
      _ ≤ B + B := add_le_add hZ_abs hmean_abs
      _ = 2 * B := by ring
  have hY_center : ∫ ω, centeredQuadraticForm μ A X ω ∂μ = 0 := by
    unfold centeredQuadraticForm
    rw [integral_sub hZ_int (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
  have h_sg :
      HasSubgaussianMGF (centeredQuadraticForm μ A X)
        ⟨(2 * B) ^ 2, sq_nonneg (2 * B)⟩ μ :=
    hasSubgaussianMGF_of_abs_le_of_integral_eq_zero hY_meas (by positivity)
      hY_bound hY_center
  refine ⟨?_, fun l _ => h_sg.integrable_exp_mul l⟩
  intro l _
  have h_cgf := h_sg.cgf_le l
  have h_const :
      ((⟨(2 * B) ^ 2, sq_nonneg (2 * B)⟩ : ℝ≥0) : ℝ) * l ^ 2 / 2 =
        2 * B ^ 2 * l ^ 2 := by
    simp
    ring
  calc cgf (centeredQuadraticForm μ A X) μ l
      ≤ ((⟨(2 * B) ^ 2, sq_nonneg (2 * B)⟩ : ℝ≥0) : ℝ) * l ^ 2 / 2 := h_cgf
    _ = 2 * B ^ 2 * l ^ 2 := h_const
    _ ≤ C * l ^ 2 * K ^ 4 * frobNorm A ^ 2 := by
        rw [hB_def]
        exact bounded_hansonWright_cgf_constant_le A hC_bound l



end NLAlib
