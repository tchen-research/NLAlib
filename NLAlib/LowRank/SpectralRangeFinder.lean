import NLAlib.LowRank.RangeFinder
import NLAlib.LowRank.Assembly
import NLAlib.LowRank.GaussianSketch
import NLAlib.Matrix.SpectralBounds
import NLAlib.Matrix.Measurable
import NLAlib.Matrix.EckartYoung
import NLAlib.Gaussian.SketchRank
import NLAlib.Gaussian.Conditioning
import NLAlib.Gaussian.Extreme.Chevet
import NLAlib.Gaussian.InverseMoments.Mean
import NLAlib.Gaussian.InverseMoments.SpectralTail

/-!
# The deterministic range-finder bound (spectral form)

Halko–Martinsson–Tropp, *Finding structure with randomness*, SIAM Rev. 2011, Theorem 9.1 in
spectral norm: for a block decomposition `A = U₁ Σ₁ V₁ᵀ + U₂ Σ₂ V₂ᵀ`, a test matrix `Ω`,
`Ω₁ = V₁ᵀ Ω` of full row rank, `Ω₂ = V₂ᵀ Ω`, and `Q` with orthonormal columns whose range
contains `range(AΩ)`,

  `‖(I − QQᵀ)A‖² ≤ ‖Σ₂‖² + ‖Σ₂ Ω₂ Ω₁†‖²`

(`specNorm_residual_sq_le_of_range_subset`), and the unsquared consequence
`‖(I − QQᵀ)A‖ ≤ ‖Σ₂‖ + ‖Σ₂ Ω₂ Ω₁†‖` (`specNorm_residual_le_of_range_subset`) used by the
expected spectral-error bound (HMT 2011, Thm 10.6).

The hypotheses are exactly those of the Frobenius form `frobSq_residual_le_of_range_subset`
(`NLAlib.LowRank.RangeFinder`): no diagonality, no conditions on `U₁`, no `U₁ᵀU₂ = 0`, no
completeness `V₁V₁ᵀ + V₂V₂ᵀ = I`, and `Σ₁` need not be invertible. The proof is the competitor
argument of HMT §9.2: with `Z = AΩΩ₁†V₁ᵀ ∈ range Q`, `‖(I − QQᵀ)A‖ ≤ ‖A − Z‖`; then
`A − Z = U₂(Σ₂V₂ᵀ − Σ₂Ω₂Ω₁†V₁ᵀ)` and the two summands have orthogonal rows (`V₂ᵀV₁ = 0`), so the
block bound `specNorm_add_sq_le_of_mul_transpose_eq_zero` applies. It avoids the
perturbation-theoretic route (`Σ₁⁻¹`, Weyl) of HMT's printed proof.

## Expected spectral error with a Gaussian test matrix (HMT 2011, Thm 10.6)

For an `n × (k + p)` standard Gaussian `Ω`, `k, p ≥ 2`, and the same block decomposition,
`E‖(I − QQᵀ)A‖ ≤ (1 + √(k/(p−1)))‖Σ₂‖ + (e√(k+p)/p)‖Σ₂‖_F`
(`integral_specNorm_residual_le_of_gaussian`). Proof: the unsquared deterministic bound, then
conditioning on `Ω₁ = V₁ᵀΩ` (independent of `Ω₂ = V₂ᵀΩ`), Chevet's inequality
`E‖Σ₂Ω₂T‖ ≤ ‖Σ₂‖‖T‖_F + ‖Σ₂‖_F‖T‖` for fixed `T = Ω₁†`, and the inverse moments
`E‖Ω₁†‖_F ≤ √(E‖Ω₁†‖_F²) = √(k/(p−1))`, `E‖Ω₁†‖ ≤ e√(k+p)/p`
(`integrable_and_integral_specNorm_mul_block_mul_pinvR_block_le`).

Atlas: `hmt-9-1-spectral` (depends on `projection-facts`, `pseudoinverse`, `norms-frob-spec`);
`rsvd-spectral-expected` (new; depends on `hmt-9-1-spectral`, `chevet`,
`pinv-spectral-expectation`, `pinv-frob-moment`, `gaussian-conditioning`).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {m n r r' t q : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype r'] [Fintype t]
  [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq r']
  [DecidableEq q] {k : ℕ}

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq r'] in
/-- The competitor identity of the range-finder proof: `A − AΩΩ₁†V₁ᵀ = U₂(Σ₂V₂ᵀ − Σ₂Ω₂Ω₁†V₁ᵀ)`
when `A = U₁Σ₁V₁ᵀ + U₂Σ₂V₂ᵀ`, `Ω₁ = V₁ᵀΩ` has full row rank and `Ω₂ = V₂ᵀΩ`. HMT 2011, proof of
Thm 9.1 (§9.2). Atlas `hmt-9-1-spectral`, `hmt-9-1-frobenius`. -/
theorem sub_mul_pinvR_mul_transpose_eq {A : Matrix m n ℝ} {U₁ : Matrix m (Fin k) ℝ}
    {U₂ : Matrix m r ℝ} {V₁ : Matrix n (Fin k) ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ)
    {Ω : Matrix n t ℝ} {Ω₁ : Matrix (Fin k) t ℝ} {Ω₂ : Matrix r' t ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ)) :
    A - A * Ω * pinvR Ω₁ * V₁ᵀ = U₂ * (S₂ * V₂ᵀ - S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ) := by
  have hZ : A * Ω * pinvR Ω₁ * V₁ᵀ = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ := by
    rw [mul_eq_mul_add_mul_of_eq_add hA Ω, ← hΩ₁, ← hΩ₂, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_assoc (U₁ * S₁) Ω₁, mul_pinvR hunit, Matrix.mul_one]
  rw [hZ, hA, Matrix.mul_sub]
  simp only [Matrix.mul_assoc]
  abel

/-- **Deterministic range-finder bound, spectral form** (HMT 2011, Thm 9.1, spectral case): if
`A = U₁Σ₁V₁ᵀ + U₂Σ₂V₂ᵀ`, `Ω₁ = V₁ᵀΩ` has full row rank, `Ω₂ = V₂ᵀΩ`, `QᵀQ = I` and
`range(AΩ) ⊆ range(Q)`, then `‖(I − QQᵀ)A‖² ≤ ‖Σ₂‖² + ‖Σ₂Ω₂Ω₁†‖²`.

Deviations from the printed statement: the hypotheses are those of the Frobenius form
`frobSq_residual_le_of_range_subset`, verbatim (block decomposition with `U₂ᵀU₂ = I`,
`V₁ᵀV₁ = I`, `V₂ᵀV₂ = I`, `V₁ᵀV₂ = 0`; no diagonality, no conditions on `U₁`, no completeness;
`Σ₁` need not be invertible); `P_Y` is `QQᵀ` for any orthonormal `Q` with
`range(AΩ) ⊆ range(Q)`; index types other than the rank `Fin k` are arbitrary `Fintype`s.
Atlas `hmt-9-1-spectral` (assumed → proved). -/
theorem specNorm_residual_sq_le_of_range_subset {A : Matrix m n ℝ} {U₁ : Matrix m (Fin k) ℝ}
    {U₂ : Matrix m r ℝ} {V₁ : Matrix n (Fin k) ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    {Ω : Matrix n t ℝ} {Ω₁ : Matrix (Fin k) t ℝ} {Ω₂ : Matrix r' t ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ))
    {Q : Matrix m q ℝ} (hQo : HasOrthonormalCols Q) (hQ : Q * (Qᵀ * (A * Ω)) = A * Ω) :
    specNorm (residual Q A) ^ 2 ≤ specNorm S₂ ^ 2 + specNorm (S₂ * Ω₂ * pinvR Ω₁) ^ 2 := by
  set Z := A * Ω * pinvR Ω₁ * V₁ᵀ with hZdef
  -- Step 1: `Z ∈ range Q`, so the residual of `A` is the residual of `A − Z`.
  have hQZ : Q * (Qᵀ * Z) = Z := by
    have : Z = A * Ω * (pinvR Ω₁ * V₁ᵀ) := Matrix.mul_assoc _ _ _
    rw [this, ← Matrix.mul_assoc Qᵀ, ← Matrix.mul_assoc Q, hQ]
  have hres : residual Q A = (A - Z) - Q * (Qᵀ * (A - Z)) := by
    rw [residual, Matrix.mul_sub, Matrix.mul_sub, hQZ]
    abel
  have h1 : specNorm (residual Q A) ≤ specNorm (A - Z) := by
    rw [hres]; exact specNorm_sub_mul_transpose_mul_le hQo _
  -- Step 2: `A − Z = U₂ W`, and `U₂` is an isometry.
  have h2 : specNorm (A - Z) =
      specNorm (S₂ * V₂ᵀ + -(S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ)) := by
    rw [hZdef, sub_mul_pinvR_mul_transpose_eq hA hΩ₁ hΩ₂ hunit,
      specNorm_mul_left_of_hasOrthonormalCols hU₂, sub_eq_add_neg]
  -- Step 3: the two summands have orthogonal rows.
  have horth : (S₂ * V₂ᵀ) * (-(S₂ * Ω₂ * pinvR Ω₁ * V₁ᵀ))ᵀ = 0 := by
    have hV' : V₂ᵀ * V₁ = 0 := transpose_mul_eq_zero_comm.1 hV
    rw [Matrix.transpose_neg, Matrix.mul_neg, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc S₂, ← Matrix.mul_assoc V₂ᵀ, hV', Matrix.zero_mul, Matrix.mul_zero, neg_zero]
  have h3 := specNorm_add_sq_le_of_mul_transpose_eq_zero horth
  rw [specNorm_neg, specNorm_mul_transpose_right_of_hasOrthonormalCols hV₂,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hV₁] at h3
  calc specNorm (residual Q A) ^ 2 ≤ specNorm (A - Z) ^ 2 :=
        pow_le_pow_left₀ (specNorm_nonneg _) h1 2
    _ ≤ _ := by rw [h2]; exact h3

/-- **Range-finder bound, unsquared spectral form**: under the hypotheses of
`specNorm_residual_sq_le_of_range_subset`, `‖(I − QQᵀ)A‖ ≤ ‖Σ₂‖ + ‖Σ₂Ω₂Ω₁†‖`
(from `√(a² + b²) ≤ a + b`). This is the form used in HMT 2011, proof of Thm 10.6.
Atlas `hmt-9-1-spectral`. -/
theorem specNorm_residual_le_of_range_subset {A : Matrix m n ℝ} {U₁ : Matrix m (Fin k) ℝ}
    {U₂ : Matrix m r ℝ} {V₁ : Matrix n (Fin k) ℝ} {V₂ : Matrix n r' ℝ}
    {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix r r' ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    {Ω : Matrix n t ℝ} {Ω₁ : Matrix (Fin k) t ℝ} {Ω₂ : Matrix r' t ℝ}
    (hΩ₁ : Ω₁ = V₁ᵀ * Ω) (hΩ₂ : Ω₂ = V₂ᵀ * Ω) (hunit : IsUnit (Ω₁ * Ω₁ᵀ))
    {Q : Matrix m q ℝ} (hQo : HasOrthonormalCols Q) (hQ : Q * (Qᵀ * (A * Ω)) = A * Ω) :
    specNorm (residual Q A) ≤ specNorm S₂ + specNorm (S₂ * Ω₂ * pinvR Ω₁) := by
  have h := specNorm_residual_sq_le_of_range_subset hA hU₂ hV₁ hV₂ hV hΩ₁ hΩ₂ hunit hQo hQ
  have ha := specNorm_nonneg S₂
  have hb := specNorm_nonneg (S₂ * Ω₂ * pinvR Ω₁)
  have hc := specNorm_nonneg (residual Q A)
  nlinarith

section Expected

open MeasureTheory ProbabilityTheory

open scoped Matrix.Norms.L2Operator in
/-- `z ↦ ‖f z‖₂` is measurable when every entry of `f` is. Proof-local. -/
private theorem measurable_specNorm_of_entries' {γ a b : Type*} [MeasurableSpace γ] [Fintype a]
    [Fintype b] [DecidableEq a] [DecidableEq b] {f : γ → Matrix a b ℝ}
    (hf : ∀ i j, Measurable fun z => f z i j) : Measurable fun z => specNorm (f z) := by
  have h1 : Measurable fun z => Matrix.of.symm (f z) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hf i j
  have h2 : Continuous (fun M : a → b → ℝ => ‖Matrix.of M‖) := continuous_norm.comp continuous_id
  exact h2.measurable.comp h1

/-- `E‖G†‖_F ≤ √(k/(p−1))` (with integrability) for a `k × (k+p)` standard Gaussian `G`,
`p ≥ 2`: Jensen and `E‖G†‖_F² = k/(p−1)`. HMT 2011, Prop 10.2 and proof of Thm 10.6.
Atlas `rsvd-spectral-expected` (uses `pinv-frob-moment`). -/
theorem integrable_and_integral_frobNorm_pinvR_gaussianMatrix_le {k p : ℕ} (hp : 2 ≤ p) :
    Integrable (fun G : Fin k → Fin (k + p) → ℝ => frobNorm (pinvR (Matrix.of G)))
      (gaussianMatrix k (k + p)) ∧
    ∫ G, frobNorm (pinvR (Matrix.of G)) ∂(gaussianMatrix k (k + p))
      ≤ Real.sqrt (k / ((p : ℝ) - 1)) := by
  obtain ⟨hsqi, hsqv⟩ := integrable_and_integral_frobSq_pinvR_gaussianMatrix
    (r := k) (k := k + p) (by omega)
  have hm : Measurable fun G : Fin k → Fin (k + p) → ℝ => frobNorm (pinvR (Matrix.of G)) :=
    Real.continuous_sqrt.measurable.comp
      (measurable_frobSq_of_entries fun i j => measurable_pinvR_entry i j)
  have hsq : (fun G : Fin k → Fin (k + p) → ℝ => frobNorm (pinvR (Matrix.of G)) ^ 2) =
      fun G => frobSq (pinvR (Matrix.of G)) := funext fun G => frobNorm_sq _
  have hsqi' : Integrable (fun G : Fin k → Fin (k + p) → ℝ =>
      frobNorm (pinvR (Matrix.of G)) ^ 2) (gaussianMatrix k (k + p)) := by rw [hsq]; exact hsqi
  have hint : Integrable (fun G : Fin k → Fin (k + p) → ℝ => frobNorm (pinvR (Matrix.of G)))
      (gaussianMatrix k (k + p)) :=
    ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hsqi').integrable one_le_two
  refine ⟨hint, ?_⟩
  have hJ := Assembly.integral_le_sqrt_integral_sq (fun G => frobNorm_nonneg _) hint hsqi'
  rw [hsq, hsqv] at hJ
  refine hJ.trans (le_of_eq ?_)
  congr 1
  push_cast
  ring_nf

/-- **Conditioned Chevet bound.** For an `n × (k+p)` standard Gaussian `Ω`, `V₁`, `V₂` with
orthonormal, mutually orthogonal columns, `k, p ≥ 2`, and any `Σ₂`, the variable
`‖Σ₂Ω₂Ω₁†‖` (`Ω₁ = V₁ᵀΩ`, `Ω₂ = V₂ᵀΩ`) is integrable and
`E‖Σ₂Ω₂Ω₁†‖ ≤ ‖Σ₂‖√(k/(p−1)) + ‖Σ₂‖_F e√(k+p)/p`. HMT 2011, proof of Thm 10.6 (§10.3).
Atlas `rsvd-spectral-expected` (uses `chevet`, `pinv-spectral-expectation`,
`pinv-frob-moment`, `gaussian-conditioning`). -/
theorem integrable_and_integral_specNorm_mul_block_mul_pinvR_block_le
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {n k p r r' : ℕ} (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n (k + p))
    {V₁ : Matrix (Fin n) (Fin k) ℝ} {V₂ : Matrix (Fin n) (Fin r') ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (S₂ : Matrix (Fin r) (Fin r') ℝ) (hk : 2 ≤ k) (hp : 2 ≤ p) :
    Integrable (fun ω => specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) μ ∧
    ∫ ω, specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ ≤
      specNorm S₂ * Real.sqrt (k / ((p : ℝ) - 1)) +
        frobNorm S₂ * (Real.exp 1 * Real.sqrt (k + p) / p) := by
  set X : Ωs → Fin k → Fin (k + p) → ℝ :=
    fun ω => Matrix.of.symm (V₁ᵀ * Matrix.of (Matrix.of.symm (Ω ω))) with hXdef
  set Y : Ωs → Fin r' → Fin (k + p) → ℝ :=
    fun ω => Matrix.of.symm (V₂ᵀ * Matrix.of (Matrix.of.symm (Ω ω))) with hYdef
  have hXlaw : μ.map X = gaussianMatrix k (k + p) := map_block_eq_gaussianMatrix hΩ V₁ hV₁
  have hYlaw : μ.map Y = gaussianMatrix r' (k + p) := map_block_eq_gaussianMatrix hΩ V₂ hV₂
  have hind : IndepFun X Y μ := indepFun_block_of_map_eq hΩ V₁ V₂ hV₁ hV₂ hV
  have hXm := aemeasurable_of_map_eq_gaussianMatrix hXlaw
  have hYm := aemeasurable_of_map_eq_gaussianMatrix hYlaw
  set g : (Fin k → Fin (k + p) → ℝ) → (Fin r' → Fin (k + p) → ℝ) → ℝ :=
    fun x y => specNorm (S₂ * Matrix.of y * pinvR (Matrix.of x)) with hgdef
  have hfg : (fun ω => specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) =
      fun ω => g (X ω) (Y ω) := rfl
  have hgm : Measurable fun q : (Fin k → Fin (k + p) → ℝ) × (Fin r' → Fin (k + p) → ℝ) =>
      g q.1 q.2 := by
    refine measurable_specNorm_of_entries' fun i j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_
      ((measurable_pinvR_entry l j).comp measurable_fst)
    fun_prop
  -- The deterministic bound after integrating out `Ω₂`.
  set B : (Fin k → Fin (k + p) → ℝ) → ℝ := fun x =>
    specNorm S₂ * frobNorm (pinvR (Matrix.of x)) + frobNorm S₂ * specNorm (pinvR (Matrix.of x))
    with hBdef
  obtain ⟨hFi, hFv⟩ := integrable_and_integral_frobNorm_pinvR_gaussianMatrix_le (k := k) hp
  obtain ⟨hSi, hSv⟩ := integrable_and_integral_specNorm_pinvR_gaussianMatrix_le
    (r := k) (k := k + p) hk (by omega)
  have hBi : Integrable B (gaussianMatrix k (k + p)) :=
    (hFi.const_mul _).add (hSi.const_mul _)
  have hB0 : ∀ x, 0 ≤ B x := fun x =>
    add_nonneg (mul_nonneg (specNorm_nonneg _) (frobNorm_nonneg _))
      (mul_nonneg (frobNorm_nonneg _) (specNorm_nonneg _))
  set bound := specNorm S₂ * Real.sqrt (k / ((p : ℝ) - 1)) +
    frobNorm S₂ * (Real.exp 1 * Real.sqrt (k + p) / p) with hbound
  have hbound0 : 0 ≤ bound :=
    add_nonneg (mul_nonneg (specNorm_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (frobNorm_nonneg _) (by positivity))
  have hBint : ∫ x, B x ∂(gaussianMatrix k (k + p)) ≤ bound := by
    rw [hBdef, integral_add (hFi.const_mul _) (hSi.const_mul _), integral_const_mul,
      integral_const_mul]
    have hcast : ((k + p : ℕ) : ℝ) - k = p := by push_cast; ring
    have hcast' : Real.sqrt ((k + p : ℕ) : ℝ) = Real.sqrt (k + p) := by push_cast; ring_nf
    rw [hcast, hcast'] at hSv
    exact add_le_add (mul_le_mul_of_nonneg_left hFv (specNorm_nonneg _))
      (mul_le_mul_of_nonneg_left hSv (frobNorm_nonneg _))
  have hL : ∫⁻ ω, ENNReal.ofReal (g (X ω) (Y ω)) ∂μ ≤ ENNReal.ofReal bound := by
    rw [lintegral_of_indepFun hXm hYm hind (g := fun x y => ENNReal.ofReal (g x y))
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable, hXlaw, hYlaw]
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x y) ∂gaussianMatrix r' (k + p) ∂gaussianMatrix k (k + p)
        ≤ ∫⁻ x, ENNReal.ofReal (B x) ∂gaussianMatrix k (k + p) := by
          refine lintegral_mono fun x => ?_
          obtain ⟨hci, hcv⟩ :=
            integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le S₂ (pinvR (Matrix.of x))
          rw [← ofReal_integral_eq_lintegral_ofReal hci (ae_of_all _ fun _ => specNorm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hcv
      _ = ENNReal.ofReal (∫ x, B x ∂gaussianMatrix k (k + p)) :=
          (ofReal_integral_eq_lintegral_ofReal hBi (ae_of_all _ hB0)).symm
      _ ≤ ENNReal.ofReal bound := ENNReal.ofReal_le_ofReal hBint
  have hf0 : 0 ≤ᵐ[μ] fun ω => g (X ω) (Y ω) := ae_of_all _ fun _ => specNorm_nonneg _
  have hfm : AEStronglyMeasurable (fun ω => g (X ω) (Y ω)) μ :=
    (hgm.comp_aemeasurable (hXm.prodMk hYm)).aestronglyMeasurable
  have hfi : Integrable (fun ω => g (X ω) (Y ω)) μ :=
    ⟨hfm, (hasFiniteIntegral_iff_ofReal hf0).2 (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  rw [hfg]
  refine ⟨hfi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hfm]
  exact ENNReal.toReal_le_of_le_ofReal hbound0 hL

/-- **Expected spectral error of the randomized range finder** (HMT 2011, Thm 10.6): for a
block decomposition `A = U₁Σ₁V₁ᵀ + U₂Σ₂V₂ᵀ` (hypotheses of
`specNorm_residual_sq_le_of_range_subset`), an `n × (k+p)` standard Gaussian test matrix `Ω`
with `k, p ≥ 2`, and any `Q ω` with a.s. orthonormal columns and `range(AΩ) ⊆ range(Q)`,
`E‖(I − QQᵀ)A‖ ≤ (1 + √(k/(p−1)))‖Σ₂‖ + (e√(k+p)/p)‖Σ₂‖_F`.

With the SVD blocks, `‖Σ₂‖ = σ_{k+1}` and `‖Σ₂‖_F = (Σ_{j>k} σ_j²)^{1/2}`, which is HMT's
printed form. Deviations: the general block form (same hypotheses as `rsvd_main_gaussian`); no
measurability of `Q` is required (the left side is `0` if not integrable, and the bound is
nonnegative); `n`, `k`, `p`, `r`, `r'` are `Fin` sizes (Gaussian law convention).
Atlas `rsvd-spectral-expected` (new; uses `hmt-9-1-spectral`, `chevet`,
`pinv-spectral-expectation`, `pinv-frob-moment`, `gaussian-conditioning`,
`gaussian-full-rank-ae`). -/
theorem integral_specNorm_residual_le_of_gaussian
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {m' q' : Type*} [Fintype m'] [DecidableEq m'] [Fintype q'] [DecidableEq q']
    {n k p r r' : ℕ} {A : Matrix m' (Fin n) ℝ} {U₁ : Matrix m' (Fin k) ℝ}
    {U₂ : Matrix m' (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ} {V₂ : Matrix (Fin n) (Fin r') ℝ}
    {S₁ : Matrix (Fin k) (Fin k) ℝ} {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hk : 2 ≤ k) (hp : 2 ≤ p) (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n (k + p))
    (Q : Ωs → Matrix m' q' ℝ) (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω) :
    ∫ ω, specNorm (residual (Q ω) A) ∂μ ≤
      (1 + Real.sqrt (k / ((p : ℝ) - 1))) * specNorm S₂ +
        Real.exp 1 * Real.sqrt (k + p) / p * frobNorm S₂ := by
  obtain ⟨hint, hle⟩ :=
    integrable_and_integral_specNorm_mul_block_mul_pinvR_block_le Ω hΩ hV₁ hV₂ hV S₂ hk hp
  have hunit : ∀ᵐ ω ∂μ, IsUnit ((V₁ᵀ * Ω ω) * (V₁ᵀ * Ω ω)ᵀ) :=
    ae_isUnit_block hΩ V₁ hV₁ (by omega)
  have hpt : (fun ω => specNorm (residual (Q ω) A)) ≤ᵐ[μ]
      fun ω => specNorm S₂ + specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) := by
    filter_upwards [hQo, hQr, hunit] with ω hqo hqr hu
    exact specNorm_residual_le_of_range_subset hA hU₂ hV₁ hV₂ hV rfl rfl hu hqo hqr
  have hmono : ∫ ω, specNorm (residual (Q ω) A) ∂μ ≤
      ∫ ω, (specNorm S₂ + specNorm (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ fun ω => specNorm_nonneg _)
      ((integrable_const (specNorm S₂)).add hint) hpt
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul] at hmono
  refine hmono.trans ?_
  have := hle
  nlinarith [specNorm_nonneg S₂, frobNorm_nonneg S₂]

/-- **SVD right blocks with spectral tail.** For `k ≤ n` every real `A` splits as
`A = U₁V₁ᵀ + U₂Σ₂V₂ᵀ` with `U₂`, `V₁`, `V₂` orthonormal, `V₁ᵀV₂ = 0`, `‖Σ₂‖ = σ_{k+1}` and
`‖Σ₂‖_F² = ∑_{j>k} σ_j²` (zero-indexed `singularValues A k`, `singularValueTailSq A k`). The
blocks are those of `exists_svd_right_blocks` (`U₁ = AV₁`, `U₂ = U`), with the spectral tail
identified through `IsSVD.specNorm_sub_truncatedMatrix`. HMT 2011, §2.1 and Thm 9.1.
Atlas `rsvd-spectral-expected` (helper; uses `svd`, `eckart-young`; belongs in
`Matrix/SvdBlocks.lean`). -/
theorem exists_svd_right_blocks_specNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (hkn : k ≤ n) :
    ∃ (r : ℕ) (U₁ : Matrix (Fin m) (Fin k) ℝ) (U₂ : Matrix (Fin m) (Fin m) ℝ)
      (V₁ : Matrix (Fin n) (Fin k) ℝ) (V₂ : Matrix (Fin n) (Fin r) ℝ)
      (S₂ : Matrix (Fin m) (Fin r) ℝ),
      A = U₁ * (1 : Matrix (Fin k) (Fin k) ℝ) * V₁ᵀ + U₂ * S₂ * V₂ᵀ ∧
      HasOrthonormalCols U₂ ∧ HasOrthonormalCols V₁ ∧ HasOrthonormalCols V₂ ∧
      V₁ᵀ * V₂ = 0 ∧ specNorm S₂ = singularValues A k ∧
      frobSq S₂ = singularValueTailSq A k := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  obtain ⟨U, V, h⟩ := exists_isSVD A
  let V₁ : Matrix (Fin (k + r)) (Fin k) ℝ := V.submatrix id (Fin.castAdd r)
  let V₂ : Matrix (Fin (k + r)) (Fin r) ℝ := V.submatrix id (Fin.natAdd k)
  let D : Matrix (Fin m) (Fin (k + r)) ℝ := rectDiag (singularValues A)
  let S₂ : Matrix (Fin m) (Fin r) ℝ := D.submatrix id (Fin.natAdd k)
  let T : Matrix (Fin m) (Fin (k + r)) ℝ :=
    rectDiag (fun i => if i < k then 0 else singularValues A i)
  have hV₁ : HasOrthonormalCols V₁ := by
    change V₁ᵀ * V₁ = 1
    have he : V₁ᵀ * V₁ = (Vᵀ * V).submatrix (Fin.castAdd r) (Fin.castAdd r) := rfl
    rw [he, h.transpose_mul_right]
    ext i j
    simp [Matrix.one_apply, Fin.castAdd_inj]
  have hV₂ : HasOrthonormalCols V₂ := by
    change V₂ᵀ * V₂ = 1
    have he : V₂ᵀ * V₂ = (Vᵀ * V).submatrix (Fin.natAdd k) (Fin.natAdd k) := rfl
    rw [he, h.transpose_mul_right]
    ext i j
    simp [Matrix.one_apply, Fin.natAdd_inj]
  have hcross : V₁ᵀ * V₂ = 0 := by
    have he : V₁ᵀ * V₂ = (Vᵀ * V).submatrix (Fin.castAdd r) (Fin.natAdd k) := rfl
    rw [he, h.transpose_mul_right]
    ext i j
    have hij : Fin.castAdd r i ≠ Fin.natAdd k j := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp [hij]
  have hcomplete : V₁ * V₁ᵀ + V₂ * V₂ᵀ = 1 := by
    ext i j
    have he := congrArg (fun M : Matrix (Fin (k + r)) (Fin (k + r)) ℝ => M i j)
      h.mul_transpose_right
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_add,
      Matrix.add_apply, V₁, V₂, Matrix.submatrix_apply, id_eq] using he
  have hAV₂ : A * V₂ = U * S₂ := by
    have he : A * V₂ = (A * V).submatrix id (Fin.natAdd k) := rfl
    rw [h.mul_right] at he
    exact he
  have hA : A = (A * V₁) * (1 : Matrix (Fin k) (Fin k) ℝ) * V₁ᵀ + U * S₂ * V₂ᵀ := by
    calc
      A = A * (V₁ * V₁ᵀ + V₂ * V₂ᵀ) := by rw [hcomplete, Matrix.mul_one]
      _ = (A * V₁) * (1 : Matrix (Fin k) (Fin k) ℝ) * V₁ᵀ + U * S₂ * V₂ᵀ := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc A V₁, ← Matrix.mul_assoc A V₂,
          hAV₂, Matrix.mul_one]
  -- The tail block equals the tail of the SVD, `U Σ_{≥k} Vᵀ = A − A_k`.
  have hST : S₂ * V₂ᵀ = T * Vᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_add]
    have hhead : ∑ a : Fin k, T i (Fin.castAdd r a) * V j (Fin.castAdd r a) = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      simp only [T, rectDiag_apply, Fin.val_castAdd]
      split_ifs with h1 h2
      · exact zero_mul _
      · exfalso; have := a.isLt; omega
      · exact zero_mul _
    rw [hhead, zero_add]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [S₂, D, V₂, T, Matrix.submatrix_apply, id_eq, rectDiag_apply, Fin.val_natAdd]
    split_ifs with h1 h2 <;> first | rfl | omega
  have htail : U * S₂ * V₂ᵀ = A - h.truncatedMatrix k := by
    have hsplit : A = h.truncatedMatrix k + U * T * Vᵀ := h.eq_head_add_tail k
    calc U * S₂ * V₂ᵀ = U * T * Vᵀ := by rw [Matrix.mul_assoc, hST, ← Matrix.mul_assoc]
      _ = (h.truncatedMatrix k + U * T * Vᵀ) - h.truncatedMatrix k := by abel
      _ = A - h.truncatedMatrix k := by rw [← hsplit]
  have hspec : specNorm S₂ = singularValues A k := by
    rw [← h.specNorm_sub_truncatedMatrix k, ← htail,
      specNorm_mul_transpose_right_of_hasOrthonormalCols hV₂,
      specNorm_mul_left_of_hasOrthonormalCols h.transpose_mul_left]
  have hfrob : frobSq S₂ = singularValueTailSq A k := by
    rw [← h.frobSq_sub_truncatedMatrix k, ← htail, frobSq_mul_right_of_orthonormal hV₂,
      frobSq_mul_left_of_orthonormal h.transpose_mul_left]
  exact ⟨r, A * V₁, U, V₁, V₂, S₂, hA, h.transpose_mul_left, hV₁, hV₂, hcross, hspec, hfrob⟩

/-- **Expected spectral error of the randomized range finder, singular-value form**
(HMT 2011, Thm 10.6): for `A ∈ ℝ^{m×n}`, `k, p ≥ 2`, `k ≤ n`, an `n × (k+p)` standard Gaussian
`Ω` and any `Q ω` with a.s. orthonormal columns and `range(AΩ) ⊆ range(Q)`,
`E‖(I − QQᵀ)A‖ ≤ (1 + √(k/(p−1)))σ_{k+1} + (e√(k+p)/p)(Σ_{j>k} σ_j²)^{1/2}`
(zero-indexed: `singularValues A k`, `singularValueTailSq A k`).
Deviations: `Q` is any a.s. orthonormal frame containing `range(AΩ)` (HMT: `Q = orth(AΩ)`),
no measurability of `Q` required; `k ≤ n` is assumed (for `k > n` the error is `0` a.s.).
Atlas `rsvd-spectral-expected`. -/
theorem integral_specNorm_residual_le_singularValues_of_gaussian
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {q' : Type*} [Fintype q'] [DecidableEq q'] {m n k p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hk : 2 ≤ k) (hp : 2 ≤ p) (hkn : k ≤ n) (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n (k + p))
    (Q : Ωs → Matrix (Fin m) q' ℝ) (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω) :
    ∫ ω, specNorm (residual (Q ω) A) ∂μ ≤
      (1 + Real.sqrt (k / ((p : ℝ) - 1))) * singularValues A k +
        Real.exp 1 * Real.sqrt (k + p) / p * Real.sqrt (singularValueTailSq A k) := by
  obtain ⟨r, U₁, U₂, V₁, V₂, S₂, hA, hU₂, hV₁, hV₂, hV, hspec, hfrob⟩ :=
    exists_svd_right_blocks_specNorm A k hkn
  have h := integral_specNorm_residual_le_of_gaussian hA hU₂ hV₁ hV₂ hV hk hp Ω hΩ Q hQo hQr
  rwa [hspec, frobNorm, hfrob] at h

/-- **Expected spectral error of the Gaussian range finder** (HMT 2011, Thm 10.6) for the
constructed measurable range frame `gaussianRangeFrame A (k + p)` of `AΩ`: no frame
hypothesis remains. `E‖(I − QQᵀ)A‖ ≤ (1 + √(k/(p−1)))σ_{k+1} + (e√(k+p)/p)(Σ_{j>k} σ_j²)^{1/2}`
for `k, p ≥ 2`, `k ≤ n`. Atlas `rsvd-spectral-expected` (audit G2 B2 statement). -/
theorem integral_specNorm_residual_gaussianRangeFrame_le
    {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
    {m n k p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hk : 2 ≤ k) (hp : 2 ≤ p) (hkn : k ≤ n)
    (Ω : Ωs → Matrix (Fin n) (Fin (k + p)) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n (k + p)) :
    ∫ ω, specNorm (residual (gaussianRangeFrame A (k + p) (Matrix.of.symm (Ω ω))) A) ∂μ ≤
      (1 + Real.sqrt (k / ((p : ℝ) - 1))) * singularValues A k +
        Real.exp 1 * Real.sqrt (k + p) / p * Real.sqrt (singularValueTailSq A k) :=
  integral_specNorm_residual_le_singularValues_of_gaussian A hk hp hkn Ω hΩ _
    (ae_hasOrthonormalCols_gaussianRangeFrame_of_map_eq A (fun ω => Matrix.of.symm (Ω ω)) hΩ)
    (by simpa only [Equiv.apply_symm_apply] using
      ae_project_gaussianRangeFrame_of_map_eq A (fun ω => Matrix.of.symm (Ω ω)) hΩ)

end Expected

end NLAlib
