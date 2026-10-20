import NLAlib.ForMathlib.Probability.ExponentialTailMoments
import NLAlib.Probability.Concentration.Matrix.IndependentSquareSum

/-!
# Integer moments of actual independent Hermitian square mass

The fixed-parameter matrix Chernoff tail gives every positive integer
moment of the realized sum-of-squares spectral norm. Integrability is
derived from the tail; no centering or positive variance is assumed.
This supports `independent-sum-spectrum-universality`.
-/

noncomputable section
set_option autoImplicit false

namespace NLAlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MatrixOrder ComplexOrder

open scoped Matrix.Norms.L2Operator in
private theorem measureReal_lambdaMax_sum_ge_le_fixed_chernoff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d N : ℕ} [NeZero d] (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    {L : ℝ} (hL : 0 < L) (hMeas : ∀ k, Measurable (X k))
    (hIndep : iIndepFun X μ) (hPSD : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, specNorm (X k ω) ≤ L) (t : ℝ) :
    μ.real {ω | (Real.exp 1 - 1) * lambdaMax (∑ k, ∫ ω, X k ω ∂μ) +
      L * (Real.log d + t) ≤ lambdaMax (∑ k, X k ω)} ≤ Real.exp (-t) := by
  let θ : ℝ := L⁻¹
  let g : ℝ := (Real.exp 1 - 1) / L
  let B := ∑ k, ∫ ω, X k ω ∂μ
  have hθ : 0 < θ := inv_pos.mpr hL
  have hg : 0 < g := div_pos (by linarith [Real.one_lt_exp_iff.mpr zero_lt_one]) hL
  have hgdef : chernoffCgfCoefficient L θ = g := by
    simp only [chernoffCgfCoefficient, if_neg hL.ne', θ, inv_mul_cancel₀ hL.ne']
    rfl
  have hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian :=
    fun k => (hPSD k).mono fun _ h => h.isHermitian
  have hSpec : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ L := by
    intro k
    filter_upwards [hPSD k, hBound k] with ω hp hb
    exact ⟨lambdaMin_nonneg_of_posSemidef hp, by rwa [hp.lambdaMax_eq_specNorm]⟩
  have hExp : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ := by
    intro k
    let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    have hc : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A)) := by
      dsimp [matrixExp]
      fun_prop
    refine Integrable.of_bound (hc.comp_aestronglyMeasurable (hMeas k).aestronglyMeasurable)
      (Real.exp (θ * L)) ?_
    filter_upwards [hHerm k, hSpec k] with ω hH hB
    rw [matrixExp_smul_eq_cfc (X k ω) hH]
    apply norm_cfc_le (Real.exp_pos _).le
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ.le
    have hf : (spectrum ℝ (X k ω)).Finite := by
      rw [hH.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact (le_csSup hf.bddAbove hx).trans hB.2
  have hBH : B.IsHermitian := by
    apply isSelfAdjoint_sum
    intro k _
    exact (Matrix.nonneg_iff_posSemidef.mp
      (integral_nonneg_of_ae ((hPSD k).mono fun _ h => h.nonneg))).isHermitian
  have hcumH : (cumulantSum μ X θ).IsHermitian := by
    apply isSelfAdjoint_sum
    intro k _
    unfold matrixLog
    exact IsSelfAdjoint.cfc
  have hcum : cumulantSum μ X θ ≤ g • B := by
    have hk := fun k => (chernoff_matrix_mgf_cgf_le μ (X k) L hL.le
      (hMeas k) (hHerm k) (hSpec k) θ).2
    unfold cumulantSum
    rw [Matrix.le_iff]
    dsimp only [B]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Matrix.posSemidef_sum
    intro k _
    simpa only [hgdef] using (Matrix.le_iff.mp (hk k))
  have htrace : traceExp (cumulantSum μ X θ) ≤
      (d : ℝ) * Real.exp (g * lambdaMax B) := by
    calc
      _ ≤ traceExp (g • B) := traceExp_le_traceExp _ _ hcumH
        (hBH.smul (isSelfAdjoint_iff.mpr (star_trivial _))) hcum
      _ ≤ _ := by
        convert traceExp_le_card_mul_exp_lambdaMax (g • B)
          (hBH.smul (isSelfAdjoint_iff.mpr (star_trivial _))) using 1
        simp only [Fintype.card_fin, lambdaMax_smul_of_pos B hg]
  have hm := measureReal_lambdaMax_sum_ge_le_exp_mul_traceExp_cumulantSum μ X
    hθ hMeas hHerm hIndep hExp
    ((Real.exp 1 - 1) * lambdaMax B + L * (Real.log d + t))
  refine hm.trans ((mul_le_mul_of_nonneg_left htrace (Real.exp_pos _).le).trans_eq ?_)
  have hd : (0 : ℝ) < d := by exact_mod_cast (NeZero.pos d)
  have hexp : -θ * ((Real.exp 1 - 1) * lambdaMax B + L * (Real.log d + t)) +
      g * lambdaMax B = -(Real.log d + t) := by
    dsimp only [θ, g]
    field_simp [hL.ne']
    ring
  calc
    _ = (d : ℝ) * Real.exp
        (-θ * ((Real.exp 1 - 1) * lambdaMax B + L * (Real.log d + t)) +
          g * lambdaMax B) := by rw [Real.exp_add]; ring
    _ = (d : ℝ) * Real.exp (-(Real.log d + t)) := by rw [hexp]
    _ = Real.exp (-t) := by
      rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hd]
      field_simp [hd.ne']

open scoped Matrix.Norms.L2Operator in
/-- Actual independent Hermitian increments bounded by `R` have every positive
integer square-mass moment. The sharp shifted-exponential comparison gives
`(exp 1 - 1) * specNorm (sum E Z_i^2) + R^2 * (log d + q)`.
No centering or supplied integrability is required, and `R = 0` is included.
Source: the matrix-Chernoff tail underlying Brailovskaya--van Handel,
arXiv:2201.05142v3, Lemma 6.12, followed by layer cake and Minkowski.
This is an ordinary moment helper, not the full spectral universality theorem. -/
theorem memLp_and_lpNorm_specNorm_sum_sq_le_chernoff
    {Ω ι n : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype n] [DecidableEq n]
    [Nonempty n] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ι → Ω → Matrix n n ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hMeas : ∀ i, Measurable (Z i)) (hIndep : iIndepFun Z μ)
    (hHerm : ∀ i, ∀ᵐ ω ∂μ, (Z i ω).IsHermitian)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, specNorm (Z i ω) ≤ R)
    (q : ℕ) (hq : 0 < q) :
    MemLp (fun ω => specNorm (∑ i, Z i ω ^ 2)) (q : ℝ≥0∞) μ ∧
      lpNorm (fun ω => specNorm (∑ i, Z i ω ^ 2)) (q : ℝ≥0∞) μ ≤
        (Real.exp 1 - 1) * specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) +
          R ^ 2 * (Real.log (Fintype.card n) + q) := by
  classical
  have hSqMeas : Measurable (fun A : Matrix n n ℂ => A ^ 2) := by
    simpa only [pow_two, id_eq] using
      (measurable_id.matrix_mul measurable_id : Measurable (fun A : Matrix n n ℂ => A * A))
  have hMassMeas : Measurable (fun ω => specNorm (∑ i, Z i ω ^ 2)) := by
    simpa only [specNorm_eq_norm, Finset.sum_apply, Function.comp_apply] using
      (Finset.measurable_sum Finset.univ fun i _ => hSqMeas.comp (hMeas i)).norm
  rcases eq_or_lt_of_le hR with hR0 | hRp
  · subst R
    have hZ : ∀ i, Z i =ᵐ[μ] 0 := by
      intro i
      filter_upwards [hBound i] with ω hω
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [specNorm_eq_norm] using hω
    have hMass : (fun ω => specNorm (∑ i, Z i ω ^ 2)) =ᵐ[μ] 0 := by
      filter_upwards [ae_all_iff.mpr hZ] with ω hω
      simp [hω, specNorm_zero]
    have hMean : (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply integral_eq_zero_of_ae
      exact (hZ i).mono fun ω hω => by simp [hω]
    refine ⟨(memLp_congr_ae hMass).mpr MemLp.zero, ?_⟩
    rw [← toReal_eLpNorm hMassMeas.aestronglyMeasurable,
      eLpNorm_congr_ae hMass]
    simp [hMean, specNorm_zero]
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
  let : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  let e := Fintype.equivFin n
  let f := (Fintype.equivFin ι).symm
  let E : Matrix n n ℂ ≃ₗ[ℝ] Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    Matrix.reindexLinearEquiv ℝ ℂ e e
  let Y : Fin (Fintype.card ι) → Ω →
      Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    fun k ω => E (Z (f k) ω ^ 2)
  have hEMeas : Measurable E := E.toContinuousLinearEquiv.continuous.measurable
  have hYMeas : ∀ k, Measurable (Y k) :=
    fun k => hEMeas.comp (hSqMeas.comp (hMeas (f k)))
  have hYIndep : iIndepFun Y μ :=
    (iIndepFun.precomp f.injective hIndep).comp
      (fun _ A => E (A ^ 2)) (fun _ => hEMeas.comp hSqMeas)
  have hYPSD : ∀ k, ∀ᵐ ω ∂μ, (Y k ω).PosSemidef :=
    fun k => (hSqPSD (f k)).mono fun _ h => h.submatrix e.symm
  have hYBound : ∀ k, ∀ᵐ ω ∂μ, specNorm (Y k ω) ≤ R ^ 2 := by
    intro k
    filter_upwards [hSqBound (f k)] with ω hb
    change specNorm ((Z (f k) ω ^ 2).reindex e e) ≤ R ^ 2
    rwa [specNorm_reindex]
  have hYsum (ω : Ω) : (∑ k, Y k ω) = E (∑ i, Z i ω ^ 2) := by
    change (∑ k, E (Z (f k) ω ^ 2)) = _
    rw [← map_sum]
    exact congrArg E (f.sum_comp (fun i => Z i ω ^ 2))
  have hYmean : (∑ k, ∫ ω, Y k ω ∂μ) = E (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) := by
    calc
      _ = ∑ k, E (∫ ω, Z (f k) ω ^ 2 ∂μ) := by
        apply Finset.sum_congr rfl
        intro k _
        exact integral_reindex μ e (fun ω => Z (f k) ω ^ 2)
      _ = E (∑ k, ∫ ω, Z (f k) ω ^ 2 ∂μ) := (map_sum E _ _).symm
      _ = _ := congrArg E (f.sum_comp (fun i => ∫ ω, Z i ω ^ 2 ∂μ))
  have hSumPSD : ∀ᵐ ω ∂μ, (∑ i, Z i ω ^ 2).PosSemidef := by
    filter_upwards [ae_all_iff.mpr hSqPSD] with ω hω
    exact Matrix.posSemidef_sum _ (fun i _ => hω i)
  have hMeanPSD : (∑ i, ∫ ω, Z i ω ^ 2 ∂μ).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    rw [← Matrix.nonneg_iff_posSemidef]
    exact integral_nonneg_of_ae ((hSqPSD i).mono fun _ h => h.nonneg)
  have hLeft : (fun ω => lambdaMax (∑ k, Y k ω)) =ᵐ[μ]
      fun ω => specNorm (∑ i, Z i ω ^ 2) := by
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
  let a := (Real.exp 1 - 1) * specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) +
    R ^ 2 * Real.log (Fintype.card n)
  have ha : 0 ≤ a := by
    apply add_nonneg
    · exact mul_nonneg (by linarith [Real.one_lt_exp_iff.mpr zero_lt_one]) (specNorm_nonneg _)
    · exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by
        exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card n))))
  have hTail : ∀ t : ℝ, 0 < t →
      μ.real {ω | a + R ^ 2 * t < specNorm (∑ i, Z i ω ^ 2)} ≤ Real.exp (-t) := by
    intro t _ht
    have hc := measureReal_lambdaMax_sum_ge_le_fixed_chernoff μ Y (sq_pos_of_pos hRp)
      hYMeas hYIndep hYPSD hYBound t
    rw [hRight] at hc
    have he : μ.real {ω | a + R ^ 2 * t ≤ specNorm (∑ i, Z i ω ^ 2)} =
        μ.real {ω | (Real.exp 1 - 1) * specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) +
          R ^ 2 * (Real.log (Fintype.card n) + t) ≤ lambdaMax (∑ k, Y k ω)} := by
      apply measureReal_congr
      filter_upwards [hLeft] with ω hω
      apply propext
      change (a + R ^ 2 * t ≤ specNorm (∑ i, Z i ω ^ 2)) ↔
        ((Real.exp 1 - 1) * specNorm (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) +
          R ^ 2 * (Real.log (Fintype.card n) + t) ≤ lambdaMax (∑ k, Y k ω))
      rw [hω]
      dsimp only [a]
      ring_nf
    calc
      _ ≤ μ.real {ω | a + R ^ 2 * t ≤ specNorm (∑ i, Z i ω ^ 2)} := by
        refine measureReal_mono ?_ (measure_ne_top μ _)
        intro ω hω
        change a + R ^ 2 * t < specNorm (∑ i, Z i ω ^ 2) at hω
        change a + R ^ 2 * t ≤ specNorm (∑ i, Z i ω ^ 2)
        exact hω.le
      _ ≤ _ := he.symm ▸ hc
  obtain ⟨hm, hn⟩ := memLp_and_lpNorm_le_of_shifted_exponential_tail μ _
    hMassMeas.aemeasurable (fun _ => specNorm_nonneg _) ha (sq_pos_of_pos hRp) hTail q hq
  refine ⟨hm, hn.trans_eq ?_⟩
  dsimp only [a]
  ring

end NLAlib
