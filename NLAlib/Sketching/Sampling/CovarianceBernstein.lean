import NLAlib.Sketching.Sampling.LeverageSampling
import NLAlib.Probability.Concentration.Matrix.FiniteHermitianBernstein
import NLAlib.Matrix.Norms.LoewnerBounds
import NLAlib.Matrix.Spectral.PositiveTraceNorm
import NLAlib.Matrix.Norms.Complexification
import NLAlib.Matrix.Spectral.Complexification

/-!
# Bernstein bounds for an actually sampled covariance

Inverse-probability row samples under the finite product sampling law give independent
rank-one covariance samples. Row-score domination supplies the sharp centered norm and
variance bounds used by ridge sampling, without changing the actual sampling distribution.

Source: Tropp 2015, Theorem 6.1.1; Cohen–Musco–Musco 2017, Theorem 5; the finite covariance
derivation is `sketching_lowrank_routes_2026_10_24/sketching.tex`, ridge-sampling section.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder NNReal ENNReal

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

private theorem conjTranspose_map_ofReal_mul_self (D : Matrix m n ℝ) :
    (D.map Complex.ofReal)ᴴ * D.map Complex.ofReal =
      (realMatrixComplexification (Dᵀ * D) : Matrix n n ℂ) := by
  ext a b
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    realMatrixComplexification_apply, Complex.ofReal_sum]

omit [Fintype m] [DecidableEq n] in
private theorem posSemidef_columnRowSample_gram (C : Matrix m n ℂ) (p : m → ℝ≥0) (i : m) :
    (columnRowSample Cᴴ C p i).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_star_self (C i)).smul (inv_nonneg.mpr (p i).coe_nonneg)

omit [Fintype m] [DecidableEq n] in
private theorem re_trace_columnRowSample_gram (C : Matrix m n ℂ) (p : m → ℝ≥0) (i : m) :
    (columnRowSample Cᴴ C p i).trace.re = (∑ a, ‖C i a‖ ^ 2) / p i := by
  simp only [columnRowSample, Matrix.trace, Matrix.diag, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Complex.smul_re, Complex.re_sum,
    smul_eq_mul]
  change (∑ a, (p i : ℝ)⁻¹ * (star (C i a) * C i a).re) = _
  have hnorm (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    have hz : (Complex.normSq z : ℂ) = star z * z := Complex.normSq_eq_conj_mul_self
    have h := congrArg Complex.re hz
    simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using h.symm
  rw [div_eq_mul_inv, mul_comm _ (p i : ℝ)⁻¹, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hnorm]

omit [Fintype m] in
private theorem sq_columnRowSample_gram (C : Matrix m n ℂ) (p : m → ℝ≥0) (i : m) :
    columnRowSample Cᴴ C p i ^ 2 =
      ((∑ a, ‖C i a‖ ^ 2) / (p i : ℝ)) • columnRowSample Cᴴ C p i := by
  have hdot : (fun b => C i b) ⬝ᵥ (fun a => star (C i a)) =
      ((∑ a, ‖C i a‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, RCLike.star_def, RCLike.mul_conj, Complex.ofReal_sum,
      Complex.ofReal_pow]
    rfl
  simp only [columnRowSample, pow_two, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.conjTranspose_apply, hdot, Matrix.vecMulVec_smul]
  ext a b
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Complex.real_smul,
    smul_eq_mul, div_eq_mul_inv]
  push_cast
  ring

private theorem sum_smul_sub_sq {p : m → ℝ≥0} (hp : ∑ i, p i = 1)
    (W : m → Matrix n n ℂ) (M : Matrix n n ℂ) (hmean : ∑ i, (p i : ℝ) • W i = M) :
    (∑ i, (p i : ℝ) • (W i - M) ^ 2) = (∑ i, (p i : ℝ) • W i ^ 2) - M ^ 2 := by
  have hright : (∑ i, (p i : ℝ) • (W i * M)) = M * M := by
    simp only [← Matrix.smul_mul]
    rw [← Finset.sum_mul, hmean]
  have hleft : (∑ i, (p i : ℝ) • (M * W i)) = M * M := by
    simp only [← Matrix.mul_smul]
    rw [← Finset.mul_sum, hmean]
  have hconst : (∑ i, (p i : ℝ) • M ^ 2) = M ^ 2 := by
    rw [← Finset.sum_smul]
    have hp' : ∑ i, (p i : ℝ) = 1 := by exact_mod_cast hp
    rw [hp', one_smul]
  have hexp (i : m) : (W i - M) ^ 2 = W i ^ 2 - W i * M - M * W i + M ^ 2 := by
    noncomm_ring
  simp_rw [hexp, smul_add, smul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hright, hleft, hconst]
  noncomm_ring

private theorem covariance_sample_properties (C : Matrix m n ℂ) (p : m → ℝ≥0)
    (hp : ∑ i, p i = 1) {t : ℝ} (ht : 0 < t)
    (hdom : ∀ i, (∑ a, ‖C i a‖ ^ 2) ≤ t * (p i : ℝ)) :
    (∑ i, (p i : ℝ) • columnRowSample Cᴴ C p i) = Cᴴ * C ∧
      (∀ i, columnRowSample Cᴴ C p i ≤ t • (1 : Matrix n n ℂ)) ∧
      Cᴴ * C ≤ t • (1 : Matrix n n ℂ) ∧
      (∑ i, (p i : ℝ) • (columnRowSample Cᴴ C p i) ^ 2) ≤ t • (Cᴴ * C) := by
  classical
  let W := columnRowSample Cᴴ C p
  have htrace (i : m) : (W i).trace.re ≤ t := by
    rw [re_trace_columnRowSample_gram]
    by_cases hi : (p i : ℝ) = 0
    · rw [hi, div_zero]
      exact ht.le
    · exact (div_le_iff₀ (lt_of_le_of_ne (p i).coe_nonneg (Ne.symm hi))).mpr (hdom i)
  have hW (i : m) : W i ≤ t • (1 : Matrix n n ℂ) :=
    ((posSemidef_columnRowSample_gram C p i).specNorm_le_iff ht.le).mp
      ((posSemidef_columnRowSample_gram C p i).specNorm_le_re_trace.trans (htrace i))
  have hsupport : ∀ i, p i = 0 →
      Matrix.vecMulVec (fun a => Cᴴ a i) (fun b => C i b) = 0 := by
    intro i hi
    have hq : ∑ a, ‖C i a‖ ^ 2 = 0 := by
      apply le_antisymm
      · simpa only [hi, NNReal.coe_zero, mul_zero] using hdom i
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hrow (a : n) : C i a = 0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖C i a‖)).mp hq
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hh a (Finset.mem_univ a)))
    ext a b
    simp only [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, hrow, star_zero, zero_mul,
      Matrix.zero_apply]
  have hmean : (∑ i, (p i : ℝ) • W i) = Cᴴ * C :=
    sum_probability_smul_columnRowSample Cᴴ C p hsupport
  have hmass : ∑ i, (p i : ℝ) = 1 := by exact_mod_cast hp
  have hM : Cᴴ * C ≤ t • (1 : Matrix n n ℂ) := by
    rw [← hmean]
    calc
      _ ≤ ∑ i, (p i : ℝ) • (t • (1 : Matrix n n ℂ)) :=
        Finset.sum_le_sum fun i _ => smul_le_smul_of_nonneg_left (hW i) (p i).coe_nonneg
      _ = _ := by rw [← Finset.sum_smul, hmass, one_smul]
  refine ⟨hmean, hW, hM, ?_⟩
  change (∑ i, (p i : ℝ) • W i ^ 2) ≤ t • (Cᴴ * C)
  rw [← hmean, Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [smul_comm t]
  apply smul_le_smul_of_nonneg_left _ (p i).coe_nonneg
  rw [sq_columnRowSample_gram]
  exact smul_le_smul_of_nonneg_right
    (by simpa only [W, re_trace_columnRowSample_gram] using htrace i)
    (posSemidef_columnRowSample_gram C p i).nonneg

open scoped Matrix.Norms.L2Operator in
private theorem centered_covariance_sample_bounds (C : Matrix m n ℂ) (p : m → ℝ≥0)
    (hp : ∑ i, p i = 1) {t : ℝ} (ht : 0 < t)
    (hC : Cᴴ * C ≤ 1) (hdom : ∀ i, (∑ a, ‖C i a‖ ^ 2) ≤ t * (p i : ℝ)) :
    (∑ i, (p i : ℝ) • (columnRowSample Cᴴ C p i - Cᴴ * C)) = 0 ∧
      (∀ i, specNorm (columnRowSample Cᴴ C p i - Cᴴ * C) ≤ t) ∧
      (∑ i, (p i : ℝ) • (columnRowSample Cᴴ C p i - Cᴴ * C) ^ 2) ≤
        t • (1 : Matrix n n ℂ) := by
  classical
  obtain ⟨hmean, hW, hM, hsecond⟩ := covariance_sample_properties C p hp ht hdom
  have hmass : ∑ i, (p i : ℝ) = 1 := by exact_mod_cast hp
  refine ⟨?_, ?_, ?_⟩
  · simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hmean, ← Finset.sum_smul, hmass, one_smul, sub_self]
  · intro i
    apply (((posSemidef_columnRowSample_gram C p i).isHermitian.sub
      (Matrix.posSemidef_conjTranspose_mul_self C).isHermitian).specNorm_le_iff_sandwich ht.le).mpr
    constructor
    · have h := add_le_add (neg_le_neg hM) (posSemidef_columnRowSample_gram C p i).nonneg
      simpa only [add_zero, zero_add, sub_eq_add_neg, add_comm] using h
    · exact (sub_le_self _ (Matrix.posSemidef_conjTranspose_mul_self C).nonneg).trans (hW i)
  · rw [sum_smul_sub_sq hp _ _ hmean]
    have hMsq : 0 ≤ (Cᴴ * C) ^ 2 := by
      simpa only [pow_two, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
        (Matrix.posSemidef_conjTranspose_mul_self (Cᴴ * C)).nonneg
    exact (sub_le_self _ hMsq).trans (hsecond.trans
      (smul_le_smul_of_nonneg_left hC ht.le))

open scoped Matrix.Norms.L2Operator in
/-- Independent inverse-probability row samples satisfy the covariance Bernstein bound
under the actual finite product law. The probabilities may vanish, because row-score
domination forces the corresponding data rows to vanish. The dimension factor is the
ambient column dimension; no rank assumption is imposed on the data matrix.

Source: Tropp 2015, Theorem 6.1.1; Cohen–Musco–Musco 2017, Theorem 5. -/
theorem measureReal_specNorm_sampled_gram_sub_le
    [MeasurableSpace m] [MeasurableSingletonClass m] [Nonempty n]
    (C : Matrix m n ℂ) (p : m → ℝ≥0) (hp : ∑ i, p i = 1)
    {t : ℝ} (ht : 0 < t) (hC : Cᴴ * C ≤ 1)
    (hdom : ∀ i, (∑ a, ‖C i a‖ ^ 2) ≤ t * (p i : ℝ))
    {s : ℕ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin s => finiteSamplingLaw p hp)).real
      {ω | ε < specNorm ((sampledRowMatrix C p ω)ᴴ * sampledRowMatrix C p ω - Cᴴ * C)} ≤
        2 * Fintype.card n * Real.exp (-(s : ℝ) * ε ^ 2 / (2 * t * (1 + ε / 3))) := by
  classical
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  let ν := finiteSamplingLaw p hp
  let μ := Measure.pi (fun _ : Fin s => ν)
  let W := columnRowSample Cᴴ C p
  let M := Cᴴ * C
  let c : ℝ := 1 / (s : ℝ)
  let V := ∑ i, (p i : ℝ) • (W i - M) ^ 2
  let Y (i : m) := c • (W i - M)
  let Z (j : Fin s) (ω : Fin s → m) := Y (ω j)
  obtain ⟨hcenter, hbound, hvariance⟩ := centered_covariance_sample_bounds C p hp ht hC hdom
  have hc : 0 < c := one_div_pos.mpr hsR
  have hWH (i : m) : (W i - M).IsHermitian :=
    (posSemidef_columnRowSample_gram C p i).isHermitian.sub
      (Matrix.posSemidef_conjTranspose_mul_self C).isHermitian
  have hYH (i : m) : (Y i).IsHermitian :=
    (hWH i).smul (isSelfAdjoint_iff.mpr (star_trivial c))
  have hZmeas (j : Fin s) : Measurable (Z j) :=
    (show Measurable Y from Measurable.of_discrete).comp (measurable_pi_apply j)
  have hZbound (j : Fin s) : ∀ᵐ ω ∂μ, specNorm (Z j ω) ≤ t / s := by
    apply ae_of_all
    intro ω
    change specNorm (c • (W (ω j) - M)) ≤ t / s
    rw [specNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      ← specNorm_eq_norm]
    calc
      _ ≤ c * t := mul_le_mul_of_nonneg_left (hbound (ω j)) hc.le
      _ = t / s := by dsimp only [c]; ring
  have hYmean : ∫ i, Y i ∂ν = 0 := by
    change (∫ i, c • (W i - M) ∂finiteSamplingLaw p hp) = 0
    rw [integral_smul, integral_finiteSamplingLaw]
    change c • (∑ i, (p i : ℝ) • (columnRowSample Cᴴ C p i - Cᴴ * C)) = 0
    rw [hcenter, smul_zero]
  have hmean (j : Fin s) : ∫ ω, Z j ω ∂μ = 0 := by
    change (∫ ω : Fin s → m, Y (ω j) ∂Measure.pi (fun _ : Fin s => ν)) = 0
    rw [integral_comp_eval (show AEStronglyMeasurable Y ν from .of_discrete), hYmean]
  have hV : V.PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply Finset.sum_nonneg
    intro i _
    apply smul_nonneg (p i).coe_nonneg
    simpa only [pow_two, (hWH i).eq] using
      (Matrix.posSemidef_conjTranspose_mul_self (W i - M)).nonneg
  have hVnorm : specNorm V ≤ t := (hV.specNorm_le_iff ht.le).mpr hvariance
  have hYsq : (∫ i, Y i ^ 2 ∂ν) = c ^ 2 • V := by
    change (∫ i, (c • (W i - M)) ^ 2 ∂finiteSamplingLaw p hp) = _
    rw [integral_finiteSamplingLaw]
    simp only [smul_pow]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  have hvar : (∑ j, ∫ ω, Z j ω ^ 2 ∂μ) = c • V := by
    have he (j : Fin s) : (∫ ω, Z j ω ^ 2 ∂μ) = c ^ 2 • V := by
      change (∫ ω : Fin s → m, Y (ω j) ^ 2 ∂Measure.pi (fun _ : Fin s => ν)) = _
      calc
        _ = ∫ i, Y i ^ 2 ∂ν := integral_comp_eval (μ := fun _ : Fin s => ν) (i := j)
          (show AEStronglyMeasurable (fun i => Y i ^ 2) ν from .of_discrete)
        _ = _ := hYsq
    simp_rw [he]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    dsimp only [c]
    field_simp
  have hvarnorm : specNorm (∑ j, ∫ ω, Z j ω ^ 2 ∂μ) ≤ t / s := by
    rw [hvar, specNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      ← specNorm_eq_norm]
    calc
      _ ≤ c * t := mul_le_mul_of_nonneg_left hVnorm hc.le
      _ = t / s := by dsimp only [c]; ring
  have hsum (ω : Fin s → m) : ∑ j, Z j ω =
      (sampledRowMatrix C p ω)ᴴ * sampledRowMatrix C p ω - Cᴴ * C := by
    rw [sampledRowMatrix_conjTranspose, sampledColumnMatrix_mul_sampledRowMatrix]
    change (∑ j, c • (W (ω j) - M)) = c • ∑ j, W (ω j) - M
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hcs : c * (s : ℝ) = 1 := by dsimp only [c]; field_simp
    rw [hcs, one_smul]
  have htail := (integral_and_measureReal_specNorm_sum_le_bernstein_hermitian μ Z
    (div_nonneg ht.le hsR.le) hZmeas
    (iIndepFun_pi fun _ => (show AEMeasurable Y ν from Measurable.of_discrete.aemeasurable))
    (fun j => ae_of_all _ fun ω => hYH (ω j)) hZbound hmean).2 ε hε.le
  have hden : 0 < specNorm (∑ j, ∫ ω, Z j ω ^ 2 ∂μ) + t / s * ε / 3 := by
    have hn := specNorm_nonneg (∑ j, ∫ ω, Z j ω ^ 2 ∂μ)
    positivity
  have hexp : -(ε ^ 2 / 2) /
      (specNorm (∑ j, ∫ ω, Z j ω ^ 2 ∂μ) + t / s * ε / 3) ≤
        -(s : ℝ) * ε ^ 2 / (2 * t * (1 + ε / 3)) := by
    have hD : specNorm (∑ j, ∫ ω, Z j ω ^ 2 ∂μ) + t / s * ε / 3 ≤
        t / s * (1 + ε / 3) := by nlinarith only [hvarnorm]
    calc
      _ ≤ -(ε ^ 2 / 2) / (t / s * (1 + ε / 3)) := by
        apply (div_le_div_iff₀ hden (by positivity)).mpr
        exact mul_le_mul_of_nonpos_left hD (by nlinarith [sq_nonneg ε])
      _ = _ := by field_simp
  calc
    _ ≤ μ.real {ω | ε ≤ specNorm (∑ j, Z j ω)} := measureReal_mono fun ω hω => by
      change ε ≤ specNorm (∑ j, Z j ω)
      rw [hsum]
      exact hω.le
    _ ≤ bernsteinTail (2 * Fintype.card n)
        (specNorm (∑ j, ∫ ω, Z j ω ^ 2 ∂μ)) (t / s) ε := htail
    _ ≤ _ := by
      rw [bernsteinTail, if_neg hden.ne']
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

/-- The same actual covariance-sampling Bernstein bound for real matrices, transported
through the isometric entrywise complexification. Source: Tropp 2015, Theorem 6.1.1;
Cohen–Musco–Musco 2017, Theorem 5. -/
theorem measureReal_specNorm_sampled_transpose_mul_sub_le
    [MeasurableSpace m] [MeasurableSingletonClass m] [Nonempty n]
    (C : Matrix m n ℝ) (p : m → ℝ≥0) (hp : ∑ i, p i = 1)
    {t : ℝ} (ht : 0 < t) (hC : Cᵀ * C ≤ 1)
    (hdom : ∀ i, (∑ a, ‖C i a‖ ^ 2) ≤ t * (p i : ℝ))
    {s : ℕ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin s => finiteSamplingLaw p hp)).real
      {ω | ε < specNorm ((sampledRowMatrix C p ω)ᵀ * sampledRowMatrix C p ω - Cᵀ * C)} ≤
        2 * Fintype.card n * Real.exp (-(s : ℝ) * ε ^ 2 / (2 * t * (1 + ε / 3))) := by
  classical
  have hCc : (C.map Complex.ofReal)ᴴ * C.map Complex.ofReal ≤ (1 : Matrix n n ℂ) := by
    rw [conjTranspose_map_ofReal_mul_self C, ← map_one (realMatrixComplexification (𝕜 := ℂ))]
    exact (realMatrixComplexification_le_iff _ _).mpr hC
  have hdc (i : m) : ∑ a, ‖(C.map Complex.ofReal) i a‖ ^ 2 ≤ t * (p i : ℝ) := by
    simpa only [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using hdom i
  have hn (ω : Fin s → m) :
      specNorm ((sampledRowMatrix (C.map Complex.ofReal) p ω)ᴴ *
        sampledRowMatrix (C.map Complex.ofReal) p ω - (C.map Complex.ofReal)ᴴ * C.map Complex.ofReal) =
      specNorm ((sampledRowMatrix C p ω)ᵀ * sampledRowMatrix C p ω - Cᵀ * C) := by
    rw [sampledRowMatrix_map_ofReal,
      conjTranspose_map_ofReal_mul_self (sampledRowMatrix C p ω),
      conjTranspose_map_ofReal_mul_self C, ← map_sub]
    exact specNorm_map_ofReal _
  simpa only [hn] using measureReal_specNorm_sampled_gram_sub_le
    (C.map Complex.ofReal) p hp ht hCc hdc hs hε

end NLAlib
