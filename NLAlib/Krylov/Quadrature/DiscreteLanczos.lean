import NLAlib.Krylov.Quadrature.DiscreteStieltjes

/-! # Actual finite-node Lanczos and Stieltjes Jacobi construction

Distinct nodes with positive weights give grade exactly `N`. The actual diagonal Lanczos
recursion therefore produces the full orthogonal basis and the canonical moment Jacobi
matrix. The actual weighted Stieltjes procedure has the same coefficients, with an explicit
monic mass convention at beta zero and zero coupling at termination. Its computed node values
also satisfy dual orthogonality.

Source: Gautschi (2004), Theorem 1.9 and §§2.2.3.1–2.2.3.2.
Atlas: `discrete-measure-jacobi-matrix`.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Finset
open scoped Matrix

namespace NLAlib

variable {N : ℕ}

private theorem recurrenceMatrix_eq_arnoldiMatrix {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (b : n → ℝ) (q : ℕ) :
    (Matrix.of fun r (j : Fin q) => lanczosRecurrence A b j.val r) = arnoldiMatrix A b q := by
  ext r j
  simp only [Matrix.of_apply, arnoldiMatrix, lanczosRecurrence_eq_arnoldiBasis hA]

/-- The square-root weight vector has Euclidean norm equal to square-root total mass.
This is the monic beta-zero normalization in the discrete Jacobi bordered identity. -/
private theorem norm_toLp_sqrt_eq_sqrt_sum {n : Type*} [Fintype n] (w : n → ℝ)
    (hw : ∀ r, 0 ≤ w r) :
    ‖WithLp.toLp 2 (fun r => Real.sqrt (w r))‖ = Real.sqrt (∑ r, w r) := by
  have hs : ‖WithLp.toLp 2 (fun r => Real.sqrt (w r))‖ ^ 2 = ∑ r, w r := by
    rw [norm_toLp_sq_eq_dotProduct_self]
    simp only [dotProduct, ← pow_two, Real.sq_sqrt (hw _)]
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Actual Lanczos on the diagonal nodes produces an orthonormal square basis of full
order `N`, including the empty discrete measure.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem hasOrthonormalCols_lanczosRecurrence_diagonal_sqrt
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) :
    HasOrthonormalCols (Matrix.of fun r (j : Fin N) =>
      lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j.val r) := by
  rw [recurrenceMatrix_eq_arnoldiMatrix (Matrix.isHermitian_diagonal t)]
  apply hasOrthonormalCols_arnoldiMatrix
  rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- The full basis produced by actual diagonal Lanczos has orthonormal rows as well.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem lanczosRecurrence_diagonal_sqrt_mul_conjTranspose_eq_one
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) :
    let Q := Matrix.of fun r (j : Fin N) =>
      lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j.val r
    Q * Qᴴ = 1 :=
  (hasOrthonormalCols_lanczosRecurrence_diagonal_sqrt t w ht hw).mul_conjTranspose_self

/-- The actual full Lanczos basis conjugates the diagonal nodes to the canonical moment
Jacobi matrix of the atomic measure. Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem transpose_lanczosRecurrence_diagonal_sqrt_mul_diagonal_mul_eq_jacobi
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) :
    let Q := Matrix.of fun r (j : Fin N) =>
      lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j.val r
    Qᵀ * diagonal t * Q = orthogonalPolynomialJacobiMatrix
      (polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
        (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))) N := by
  dsimp only
  rw [recurrenceMatrix_eq_arnoldiMatrix (Matrix.isHermitian_diagonal t)]
  have hq : N ≤ krylovGrade (diagonal t) (fun r => Real.sqrt (w r)) := by
    rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]
  exact T_arnoldiDecomp_eq_orthogonalPolynomialJacobiMatrix (Matrix.isHermitian_diagonal t)
    (fun r => Real.sqrt (w r)) hq

/-- The full actual Lanczos basis has the positive bordered mass identity, with monic
Stieltjes beta zero equal to total mass. The first coordinate is used only in positive order.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem transpose_lanczosRecurrence_diagonal_sqrt_mulVec_sqrt_eq_single
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) (hN : 0 < N) :
    let Q := Matrix.of fun r (j : Fin N) =>
      lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j.val r
    Qᵀ *ᵥ (fun r => Real.sqrt (w r)) =
      Pi.single ⟨0, hN⟩ (Real.sqrt (discreteStieltjesMonicBeta t w 0)) := by
  dsimp only
  rw [recurrenceMatrix_eq_arnoldiMatrix (Matrix.isHermitian_diagonal t),
    discreteStieltjesMonicBeta_zero, ← norm_toLp_sqrt_eq_sqrt_sum w (fun r => (hw r).le)]
  apply transpose_arnoldiMatrix_mulVec_eq_single (diagonal t) _ hN
  rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- Before exact finite-support termination every positive-index actual Lanczos coupling
is positive. Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem lanczosBeta_diagonal_sqrt_pos (t w : Fin N → ℝ) (ht : Function.Injective t)
    (hw : ∀ r, 0 < w r) {j : ℕ} (hj0 : 0 < j) (hj : j < N) :
    0 < lanczosBeta (diagonal t) (fun r => Real.sqrt (w r)) j := by
  apply lanczosBeta_pos (Matrix.isHermitian_diagonal t) _ hj0
  rwa [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- The actual finite-node Lanczos coupling vanishes at exact order `N`.
Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem lanczosBeta_diagonal_sqrt_eq_zero (t w : Fin N → ℝ) (ht : Function.Injective t)
    (hw : ∀ r, 0 < w r) :
    lanczosBeta (diagonal t) (fun r => Real.sqrt (w r)) N = 0 := by
  apply lanczosBeta_eq_zero_of_krylovGrade_le (Matrix.isHermitian_diagonal t)
  rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- The actual weighted Stieltjes diagonal is the canonical monic moment alpha.
Source: Gautschi (2004), §2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem discreteStieltjesAlpha_eq_orthogonalRecurrenceAlpha
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) {j : ℕ} (hj : j < N) :
    discreteStieltjesAlpha t w j = orthogonalRecurrenceAlpha
      (polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
        (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))) j := by
  have hq : N ≤ krylovGrade (diagonal t) (fun r => Real.sqrt (w r)) := by
    rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]
  let D : LanczosDecomp (diagonal t) (fun r => Real.sqrt (w r)) N :=
    arnoldiDecomp (diagonal t) (fun r => Real.sqrt (w r)) N hq
  calc
    _ = lanczosAlpha (diagonal t) (fun r => Real.sqrt (w r)) j :=
      discreteStieltjesAlpha_eq_lanczosAlpha t w (fun r => (hw r).le) j
    _ = D.alpha j := lanczosAlpha_eq_alpha (Matrix.isHermitian_diagonal t) _ hq hj
    _ = _ := (D.orthogonalRecurrenceAlpha_spectralMeasure_eq_alpha (Matrix.isHermitian_diagonal t) hj).symm

/-- Positive-index monic Stieltjes betas equal the canonical moment norm ratios, including
the zero ratio at terminal order `N`. Index zero is instead the separately stated mass.
Source: Gautschi (2004), §2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem discreteStieltjesMonicBeta_eq_orthogonalRecurrenceBeta
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r)
    {j : ℕ} (hj0 : 0 < j) (hj : j ≤ N) :
    discreteStieltjesMonicBeta t w j = orthogonalRecurrenceBeta
      (polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
        (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))) j := by
  have hgrade := krylovGrade_diagonal_sqrt_eq_card t w ht hw
  have hq : N ≤ krylovGrade (diagonal t) (fun r => Real.sqrt (w r)) := hgrade.symm.le
  let D : LanczosDecomp (diagonal t) (fun r => Real.sqrt (w r)) N :=
    arnoldiDecomp (diagonal t) (fun r => Real.sqrt (w r)) N hq
  rw [discreteStieltjesMonicBeta, if_neg (ne_of_gt hj0),
    discreteStieltjesBeta_eq_lanczosBeta t w (fun r => (hw r).le)]
  by_cases hlt : j < N
  · rw [lanczosBeta_eq_beta (Matrix.isHermitian_diagonal t) _ hq hlt]
    exact (D.orthogonalRecurrenceBeta_spectralMeasure_eq_beta_sq (Matrix.isHermitian_diagonal t) hlt).symm
  · have heq : j = N := by omega
    subst j
    rw [D.orthogonalRecurrenceBeta_spectralMeasure_eq_beta_sq_of_eq_grade
      (Matrix.isHermitian_diagonal t) hgrade.symm,
      lanczosBeta_diagonal_sqrt_eq_zero t w ht hw]
    simp [LanczosDecomp.beta]

/-- The Jacobi matrix returned by the actual weighted Stieltjes procedure is the canonical
moment Jacobi matrix of the measure; the empty case is included.
Source: Gautschi (2004), §§2.2.3.1–2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem jacobiMatrix_discreteStieltjes_eq_orthogonalPolynomialJacobiMatrix
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) :
    jacobiMatrix (discreteStieltjesAlpha t w) (discreteStieltjesBeta t w) N =
      orthogonalPolynomialJacobiMatrix
        (polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
          (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))) N := by
  have hq : N ≤ krylovGrade (diagonal t) (fun r => Real.sqrt (w r)) := by
    rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]
  rw [show discreteStieltjesAlpha t w = lanczosAlpha (diagonal t) (fun r => Real.sqrt (w r))
      from funext (discreteStieltjesAlpha_eq_lanczosAlpha t w (fun r => (hw r).le)),
    show discreteStieltjesBeta t w = lanczosBeta (diagonal t) (fun r => Real.sqrt (w r))
      from funext (discreteStieltjesBeta_eq_lanczosBeta t w (fun r => (hw r).le)),
    jacobiMatrix_lanczosAlpha_lanczosBeta_eq_T (Matrix.isHermitian_diagonal t) _ hq,
    T_arnoldiDecomp_eq_orthogonalPolynomialJacobiMatrix (Matrix.isHermitian_diagonal t) _ hq]

/-- The monic coefficients returned by the normalized Stieltjes procedure assemble the same
Jacobi matrix after square-root conversion. The beta-zero mass is harmless because that
boundary coefficient is never an off-diagonal entry.
Source: Gautschi (2004), §§2.2.3.1–2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem jacobiMatrix_discreteStieltjesAlpha_sqrt_monicBeta_eq
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) :
    jacobiMatrix (discreteStieltjesAlpha t w)
      (fun j => Real.sqrt (discreteStieltjesMonicBeta t w j)) N =
      orthogonalPolynomialJacobiMatrix
        (polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
          (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))) N := by
  rw [← jacobiMatrix_discreteStieltjes_eq_orthogonalPolynomialJacobiMatrix t w ht hw]
  have hbeta (j : ℕ) : 0 ≤ discreteStieltjesBeta t w j := by
    rw [discreteStieltjesBeta_eq_lanczosBeta t w (fun r => (hw r).le)]
    exact lanczosBeta_nonneg _ _ _
  ext i j
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with hij hupper hlower
  · rfl
  · rw [discreteStieltjesMonicBeta, if_neg (by omega : j.val ≠ 0), Real.sqrt_sq (hbeta j.val)]
  · rw [discreteStieltjesMonicBeta, if_neg (by omega : i.val ≠ 0), Real.sqrt_sq (hbeta i.val)]
  · rfl

/-- Computed Stieltjes values are the actual Lanczos orthonormal polynomials evaluated at
the nodes. This identifies the value-only implementation with the polynomial procedure.
Source: Gautschi (2004), §2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem discreteStieltjesValues_eq_eval_lanczosPoly
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) {j : ℕ} (hj : j < N)
    (r : Fin N) :
    discreteStieltjesValues t w j r =
      (LanczosDecomp.poly (arnoldiDecomp (diagonal t) (fun r => Real.sqrt (w r)) N
        (by rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw])) j).eval (t r) := by
  have hq : N ≤ krylovGrade (diagonal t) (fun r => Real.sqrt (w r)) := by
    rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]
  let D : LanczosDecomp (diagonal t) (fun r => Real.sqrt (w r)) N :=
    arnoldiDecomp (diagonal t) (fun r => Real.sqrt (w r)) N hq
  have hpoly := D.Q_apply_diagonal_sqrt_eq_eval_poly_mul r ⟨j, hj⟩
  have hcur : D.Q r ⟨j, hj⟩ = lanczosRecurrence (diagonal t) (fun r => Real.sqrt (w r)) j r := by
    simp only [D, arnoldiDecomp_Q, arnoldiMatrix, lanczosRecurrence_eq_arnoldiBasis
      (Matrix.isHermitian_diagonal t), Matrix.of_apply]
  rw [hcur, lanczosRecurrence_diagonal_sqrt_eq_mul_discreteStieltjesValues t w
    (fun r => (hw r).le)] at hpoly
  exact mul_left_cancel₀ (Real.sqrt_pos.mpr (hw r)).ne' hpoly

/-- Values produced by the actual Stieltjes procedure obey the exact reciprocal-weight
dual orthogonality identity. Source: Gautschi (2004), §2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem sum_discreteStieltjesValues_mul_eq_div_weight
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ r, 0 < w r) (r s : Fin N) :
    (∑ j : Fin N, discreteStieltjesValues t w j.val r * discreteStieltjesValues t w j.val s) =
      (if r = s then 1 else 0) / w r := by
  have hq : N ≤ krylovGrade (diagonal t) (fun r => Real.sqrt (w r)) := by
    rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]
  let D : LanczosDecomp (diagonal t) (fun r => Real.sqrt (w r)) N :=
    arnoldiDecomp (diagonal t) (fun r => Real.sqrt (w r)) N hq
  have heval (j : Fin N) (r : Fin N) :
      discreteStieltjesValues t w j.val r = (D.poly j.val).eval (t r) :=
    discreteStieltjesValues_eq_eval_lanczosPoly t w ht hw j.isLt r
  simp_rw [heval]
  exact D.sum_eval_poly_mul_eval_poly_eq_div_weight hw r s

/-- The Gauss spectral-measure identity with a total mass-scaled first vector, including
the zero-point empty rule. Each eigenvector index supplies the positive dimension needed
for its first coordinate; no nonexistent coordinate is chosen at order zero.
Source: Gautschi (2004), Corollary to Theorem 3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem LanczosDecomp.spectralMeasure_T_first_total_eq_sum_dirac
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}
    (D : LanczosDecomp A b q) (hA : A.IsHermitian) :
    spectralMeasure (D.isHermitian_T hA) (fun j : Fin q => if j.val = 0 then ‖WithLp.toLp 2 b‖ else 0) =
      ∑ i : Fin q, ENNReal.ofReal ((b ⬝ᵥ b) *
        ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, Nat.zero_lt_of_lt i.isLt⟩) ^ 2) •
        Measure.dirac ((D.isHermitian_T hA).eigenvalues i) := by
  unfold spectralMeasure
  apply Finset.sum_congr rfl
  intro i _
  have hq : 0 < q := Nat.zero_lt_of_lt i.isLt
  have hfirst : (fun j : Fin q => if j.val = 0 then ‖WithLp.toLp 2 b‖ else 0) =
      Pi.single ⟨0, hq⟩ ‖WithLp.toLp 2 b‖ := by
    ext j
    simp only [Pi.single_apply, Fin.ext_iff]
  rw [hfirst, dotProduct_single, mul_pow, norm_toLp_sq_eq_dotProduct_self]
  congr 2
  ring

end NLAlib
