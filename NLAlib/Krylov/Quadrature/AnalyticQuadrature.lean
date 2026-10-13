import NLAlib.Krylov.MatrixFunctions.FunctionApprox
import NLAlib.Polynomial.FunctionApproximation.AnalyticApproximation
/-!
# Analytic Gauss quadrature and Krylov function approximation

For `f` with a bounded holomorphic extension to an open Bernstein ellipse (after rescaling the
spectral interval to `[−1, 1]`), the Chebyshev truncation (`chebyshev-approx-analytic`) and
Gauss exactness / Lanczos-FA give geometric quadrature and `f(A) v` error rates.
-/

noncomputable section

open scoped Matrix
open Polynomial Real Set

namespace NLAlib

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- **Gauss quadrature error for an analytic function**: if `f` rescaled to `[−1, 1]` has a
holomorphic extension `F` bounded by `M` on the open Bernstein ellipse of parameter `ρ > 1`,
then `|vᵀ f(A) v − (Qᵀv)ᵀ f(QᵀAQ) (Qᵀv)| ≤ 4M ρ^{1−2q}/(ρ − 1) ‖v‖²` for every orthonormal `Q`
with `K_q(A, v) ⊆ range Q` (`q ≥ 1`). Source: Trefethen (2019) [`atap`], Thm 8.2;
Golub–Meurant (2010) [`gm10`], §6.2.
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
        4 * M / ρ ^ (2 * q - 1) / (ρ - 1) * ‖WithLp.toLp 2 v‖ ^ 2 := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval
    hac hρ hFd hM hmatch (2 * q - 1)
  have hdeg : p.degree < 2 * q := hp.trans_lt (by exact_mod_cast (show 2 * q - 1 < 2 * q by omega))
  have h := abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul hA hQ v hK hdeg hspec hfp
  convert h using 1
  ring

/-- **Lanczos-FA error for an analytic function**: under the hypotheses of
`abs_dotProduct_cfc_mulVec_sub_le_of_open_bernsteinEllipse`,
`‖f(A) v − Q f(QᵀAQ) Qᵀ v‖² ≤ (4M ρ^{1−q}/(ρ − 1))² ‖v‖²`.
Source: Saad (1992) [`saad92`], Thm 3.4; Trefethen (2019) [`atap`], Thm 8.2.
Atlas: `lanczos-fa-error` (analytic rate). -/
theorem dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le_of_open_bernsteinEllipse
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (v : n → ℝ) {q : ℕ} (hq : 0 < q)
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    {f : ℝ → ℝ} {F : ℂ → ℂ} {a c ρ M : ℝ} (hac : a < c) (hρ : 1 < ρ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M)
    (hmatch : ∀ t ∈ Icc (-1 : ℝ) 1, F t = (f (((c - a) * t + c + a) / 2) : ℂ)) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ v - krylovFunApprox A f v Q)‖ ^ 2 ≤
        (4 * M / ρ ^ (q - 1) / (ρ - 1)) ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 := by
  obtain ⟨p, hp, hfp⟩ := exists_degree_le_abs_sub_eval_le_of_open_bernsteinEllipse_interval
    hac hρ hFd hM hmatch (q - 1)
  have hdeg : p.degree < q := hp.trans_lt (by exact_mod_cast (show q - 1 < q by omega))
  have h := dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le hA hQ v hK hdeg hspec hfp
  convert h using 1
  ring

end NLAlib
