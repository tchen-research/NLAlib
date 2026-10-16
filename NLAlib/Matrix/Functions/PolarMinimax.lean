import NLAlib.Matrix.Functions.PolarPolynomialHorner
import NLAlib.Matrix.Functions.PolarPolynomialWorstCase
import NLAlib.Polynomial.BestApproximation.GreedyOddMinimaxExistence
import NLAlib.Polynomial.BestApproximation.PolarMinimaxContraction

/-! # Genuine greedy minimax polar iteration and its sharp matrix guarantee

Actual scalar minimizers exist and their true attained interval images
contract by the finite Taylor competitor. The actual Gram-polynomial
matrix algorithm realizes those compositions at every rank, with the
canonical partial polar factor as its target. Source: Polar Express,
§2–§3, Theorems 3.1 and 3.3, and Appendices D–E; the exponent is `(q+1)^T`.
-/
noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- The sharp finite-step matrix estimate for any genuinely greedy minimax
coefficient sequence, with its actual interval endpoint retained.
Zero singular directions contribute zero to the canonical partial-polar error.
Source: Polar Express, Theorem 3.3 and Appendix D, corrected exponent.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem IsThinSVD.specNorm_polar_sub_greedyOddMatrixIterate_le
    {A : Matrix m n ℂ} {U : Matrix m r ℂ} {V : Matrix n r ℂ} {σ : r → ℝ}
    (hA : IsThinSVD A U V σ) {q : ℕ} {ell : ℝ} {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ}
    (h : IsGreedyOddMinimax q ell c l u) (hell : 0 < ell) (hell1 : ell < 1)
    (hσ : ∀ i, σ i ∈ Set.Icc ell 1) {T : ℕ} (hT : 1 ≤ T) :
    specNorm (canonicalPartialPolar A - oddMatrixIterate q c A T) ≤ 1 - l T ∧
      1 - l T ≤ (1 - ell ^ 2) ^ ((q + 1) ^ T) := by
  have hx := h.composition_error_le hell hell1.le hT ⟨le_rfl, hell1.le⟩
  have hE : 0 ≤ 1 - l T := (abs_nonneg _).trans hx.1
  refine ⟨hA.specNorm_polar_sub_oddMatrixIterate_le q c T hσ hE ?_, hx.2⟩
  intro x hx
  exact (h.composition_error_le hell hell1.le hT hx).1

/-- All matrix inputs with the advertised actual nonzero singular values
satisfy the sharp rate for every genuine greedy minimax sequence.
The hypotheses contain no norm-error or contraction certificate.
Source: Polar Express, Theorem 3.3, compact-SVD extension.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem specNorm_polar_sub_greedyOddMatrixIterate_le (A : Matrix m n ℂ)
    {q : ℕ} {ell : ℝ} {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ}
    (h : IsGreedyOddMinimax q ell c l u) (hell : 0 < ell) (hell1 : ell < 1)
    (hA : ∀ k, 0 < singularValues A k → singularValues A k ∈ Set.Icc ell 1)
    {T : ℕ} (hT : 1 ≤ T) :
    specNorm (canonicalPartialPolar A - oddMatrixIterate q c A T) ≤ 1 - l T ∧
      1 - l T ≤ (1 - ell ^ 2) ^ ((q + 1) ^ T) := by
  obtain ⟨U, V, ht⟩ := exists_isThinSVD A
  exact ht.specNorm_polar_sub_greedyOddMatrixIterate_le h hell hell1
    (fun i => hA i (ht.pos i)) hT

/-- With positive polynomial degree parameter, the actual greedy matrix
iterates converge to the canonical partial polar factor at every rank.
Source: Polar Express, Theorem 3.3, compact-SVD extension.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem tendsto_greedyOddMatrixIterate (A : Matrix m n ℂ)
    {q : ℕ} {ell : ℝ} {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ}
    (h : IsGreedyOddMinimax (q + 1) ell c l u) (hell : 0 < ell) (hell1 : ell < 1)
    (hA : ∀ k, 0 < singularValues A k → singularValues A k ∈ Set.Icc ell 1) :
    Tendsto (oddMatrixIterate (q + 1) c A) atTop (𝓝 (canonicalPartialPolar A)) := by
  have hb0 : 0 ≤ 1 - ell ^ 2 := by nlinarith
  have hb1 : 1 - ell ^ 2 < 1 := by nlinarith [sq_pos_of_pos hell]
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : (1 : ℕ) < (q + 1) + 1))
  have hbound : ∀ᶠ T in atTop,
      ‖canonicalPartialPolar A - oddMatrixIterate (q + 1) c A T‖ ≤
        (1 - ell ^ 2) ^ (((q + 1) + 1) ^ T) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨1, fun T hT => ?_⟩
    have he := specNorm_polar_sub_greedyOddMatrixIterate_le A h hell hell1 hA hT
    exact he.1.trans he.2
  have ht := squeeze_zero_norm' hbound hp
  have hf := (tendsto_const_nhds (x := canonicalPartialPolar A)).sub ht
  have he : (fun T => canonicalPartialPolar A -
      (canonicalPartialPolar A - oddMatrixIterate (q + 1) c A T)) =
        oddMatrixIterate (q + 1) c A := by funext T; abel
  rw [he] at hf
  simpa only [sub_zero] using hf

/-- Actual greedy coefficients exist, and their counted Horner implementation
has the source's sharp polar error and matrix-product count, at every matrix
rank. The degree parameter is `q+1 ≥ 1`, giving odd degree `2(q+1)+1`.
Source: Polar Express, §2–§3 and Appendices D–E.
atlas: polar-minimax-polynomial-iteration -/
theorem exists_greedy_polarPolynomialHorner_guarantee (q : ℕ) {ell : ℝ}
    (hell : 0 < ell) (hell1 : ell < 1) :
    ∃ (c : ℕ → ℕ → ℝ) (l u : ℕ → ℝ), IsGreedyOddMinimax (q + 1) ell c l u ∧
      ∀ (A : Matrix m n ℂ),
        (∀ k, 0 < singularValues A k → singularValues A k ∈ Set.Icc ell 1) →
        ∀ T, 1 ≤ T →
        specNorm (canonicalPartialPolar A - (polarPolynomialHornerIterate (q + 1) c A T).value) ≤
          1 - l T ∧ 1 - l T ≤ (1 - ell ^ 2) ^ (((q + 1) + 1) ^ T) ∧
          (polarPolynomialHornerIterate (q + 1) c A T).products = ((q + 1) + 1) * T := by
  obtain ⟨c, l, u, hg⟩ := exists_isGreedyOddMinimax (q + 1) hell hell1.le
  refine ⟨c, l, u, hg, fun A hA T hT => ?_⟩
  obtain ⟨he, hr⟩ := specNorm_polar_sub_greedyOddMatrixIterate_le A hg hell hell1 hA hT
  rw [← polarPolynomialHornerIterate_value] at he
  exact ⟨he, hr, polarPolynomialHornerIterate_products q c A T⟩

end NLAlib
