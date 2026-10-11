import NLAlib.Krylov.GaussQuadrature
import NLAlib.Krylov.FunctionApprox
import NLAlib.Polynomial.Exponential

/-!
# Concrete monomial and exponential Krylov error rates

The genuine scalar Chebyshev approximants supply deterministic Gauss quadrature and
matrix-function vector bounds through the existing degree-exactness interfaces.
No approximation premise is left in these concrete endpoints.
-/

noncomputable section

open scoped Matrix
open Polynomial Real
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- Monomial Gauss quadrature with the genuine compressed-polynomial rate: error at most
`4 exp(-d²/(2s)) ‖v‖²` when the degree cutoff `d` is below `2q`.
Source: Sachdeva–Vishnoi, Theorem 3.3, combined with Golub–Meurant 2010, Section 6.2;
operator rederivations `pg:operator-monomial` and `rt:quad-bound`. -/
theorem abs_dotProduct_cfc_pow_mulVec_sub_le_of_degree_cutoff {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (v : n → ℝ)
    {q s d : ℕ} (hs : 0 < s) (hd : d < 2 * q)
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (-1 : ℝ) 1) :
    |v ⬝ᵥ (cfc (fun x : ℝ => x ^ s) A *ᵥ v) -
      (Qᵀ *ᵥ v) ⬝ᵥ (cfc (fun x : ℝ => x ^ s) (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ v))| ≤
        4 * exp (-(d : ℝ) ^ 2 / (2 * s)) * (v ⬝ᵥ v) := by
  have h := abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul hA hQ v hK
    ((degree_monomialChebyshevApprox_le s d).trans_lt (by exact_mod_cast hd))
    hspec (fun _ hx => abs_pow_sub_eval_monomialChebyshevApprox_le hs d hx)
  convert h using 1
  ring

/-- Exponential Gauss quadrature has error at most `2δ ‖v‖²` once twice the Krylov dimension
exceeds the exact scalar approximation degree.
Source: Sachdeva–Vishnoi, Theorem 4.1, combined with Golub–Meurant 2010, Section 6.2;
operator rederivations `pg:operator-exponential` and `rt:quad-bound`. -/
theorem abs_dotProduct_cfc_exp_neg_mulVec_sub_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (0 : ℝ) b)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (v : n → ℝ) {q : ℕ}
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    (hq : exponentialApproxDegree b δ < 2 * q) :
    |v ⬝ᵥ (cfc (fun x : ℝ => exp (-x)) A *ᵥ v) -
      (Qᵀ *ᵥ v) ⬝ᵥ (cfc (fun x : ℝ => exp (-x)) (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ v))| ≤
        2 * δ * (v ⬝ᵥ v) :=
  abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul hA hQ v hK
    ((degree_exponentialApprox_le b δ).trans_lt (by exact_mod_cast hq)) hspec
    (fun _ hx => abs_exp_neg_sub_eval_exponentialApprox_le hb hδ hδ1 hx)

/-- Squared vector error for the matrix exponential, at the exact compressed scalar degree.
Source: Sachdeva–Vishnoi, Theorem 4.1, combined with Saad 1992, Theorem 3.3;
operator rederivations `pg:operator-exponential` and `rt:fa-bound`. -/
theorem dotProduct_cfc_exp_neg_mulVec_sub_krylovFunApprox_self_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (0 : ℝ) b)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (v : n → ℝ) {q : ℕ}
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    (hq : exponentialApproxDegree b δ < q) :
    (cfc (fun x : ℝ => exp (-x)) A *ᵥ v -
      krylovFunApprox Q A (fun x : ℝ => exp (-x)) v) ⬝ᵥ
      (cfc (fun x : ℝ => exp (-x)) A *ᵥ v -
        krylovFunApprox Q A (fun x : ℝ => exp (-x)) v) ≤ (2 * δ) ^ 2 * (v ⬝ᵥ v) :=
  dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le hA hQ v hK
    ((degree_exponentialApprox_le b δ).trans_lt (by exact_mod_cast hq)) hspec
    (fun _ hx => abs_exp_neg_sub_eval_exponentialApprox_le hb hδ hδ1 hx)

end NLAlib
