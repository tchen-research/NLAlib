import NLAlib.Krylov.GaussQuadrature
import NLAlib.Krylov.FunctionApprox
import NLAlib.Polynomial.AnalyticApproximation

/-!
# Analytic Gauss quadrature and Krylov function approximation

The original open Bernstein ellipse analyticity hypotheses supply the actual scalar
approximant, then the proved compression exactness transfers the precise geometric rate.
-/

noncomputable section

open scoped Matrix
open Polynomial Real Set
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- Analytic Lanczos quadrature has error at most `4M/(ρ^(2q-1)(ρ-1)) ‖v‖²`, the exact
source rate `4Mρ^(1-2q)/(ρ-1) ‖v‖²`, for every isometry whose range contains `K_q(A,v)`.
The rescaled function has a bounded holomorphic extension on the open Bernstein ellipse;
there is no approximation or boundary-continuity premise.
Source: Trefethen, ATAP, Theorem 8.2; Golub–Meurant 2010, Section 6.2;
operator rederivations `rt:analytic-quad`.
atlas: lanczos-quadrature-analytic-error -/
theorem abs_dotProduct_cfc_mulVec_sub_le_of_open_bernsteinEllipse
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (v : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a c ρ M : ℝ} (hac : a < c) (hρ : 1 < ρ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ t ∈ Icc (-1 : ℝ) 1, F t = (f (((c - a) * t + c + a) / 2) : ℂ)) :
    |v ⬝ᵥ (cfc f A *ᵥ v) -
      (Qᵀ *ᵥ v) ⬝ᵥ (cfc f (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ v))| ≤
        4 * M / ρ ^ (2 * q - 1) / (ρ - 1) * (v ⬝ᵥ v) := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval
    hac hρ hFd hM hmatch (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  have h := abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul hA hQ v hK hdeg hspec hfp
  convert h using 1
  ring

/-- The corresponding vector Krylov function approximation has squared error at most
`(4M/(ρ^(q-1)(ρ-1)))² ‖v‖²`, derived from genuine open-ellipse analyticity.
Source: Saad 1992, Theorem 3.3; Trefethen, ATAP, Theorem 8.2;
operator rederivations `rt:fa-bound` and `rt:analytic-approx`. -/
theorem dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le_of_open_bernsteinEllipse
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (v : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a c ρ M : ℝ} (hac : a < c) (hρ : 1 < ρ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ t ∈ Icc (-1 : ℝ) 1, F t = (f (((c - a) * t + c + a) / 2) : ℂ)) :
    (cfc f A *ᵥ v - krylovFunApprox Q A f v) ⬝ᵥ
      (cfc f A *ᵥ v - krylovFunApprox Q A f v) ≤
        (4 * M / ρ ^ (q - 1) / (ρ - 1)) ^ 2 * (v ⬝ᵥ v) := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval
    hac hρ hFd hM hmatch (q - 1)
  have hdeg : p.degree < q := hp.trans_lt (by exact_mod_cast (show q - 1 < q by omega))
  have h := dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le hA hQ v hK hdeg hspec hfp
  convert h using 1
  ring

end NLAlib
