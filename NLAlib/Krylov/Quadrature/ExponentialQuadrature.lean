import NLAlib.Krylov.MatrixFunctions.FunctionApprox
import NLAlib.Polynomial.FunctionApproximation.Exponential
/-!
# Monomial and exponential Krylov error rates

The scalar Chebyshev approximants of `x^s` and `exp(−x)` (Sachdeva–Vishnoi 2014) give Gauss
quadrature and Lanczos-FA error bounds through `lanczos-gauss-quadrature` and
`lanczos-fa-error`.
-/

noncomputable section

open scoped Matrix
open Polynomial Real

namespace NLAlib

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- **Gauss quadrature error for `x^s`**: for a symmetric `A` with spectrum in `[−1, 1]` and a
degree cutoff `d < 2q`, `|vᵀ Aˢ v − (Qᵀv)ᵀ (QᵀAQ)ˢ (Qᵀv)| ≤ 4 exp(−d²/(2s)) ‖v‖²`.
Source: Sachdeva–Vishnoi (2014) [`sv14`], Thm 3.3; Golub–Meurant (2010) [`gm10`], §6.2.
Atlas: `lanczos-gauss-quadrature` (monomial rate). -/
theorem abs_dotProduct_cfc_pow_mulVec_sub_le_of_degree_cutoff {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (v : n → ℝ)
    {q s d : ℕ} (hs : 0 < s) (hd : d < 2 * q)
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (-1 : ℝ) 1) :
    |v ⬝ᵥ (cfc (fun x : ℝ => x ^ s) A *ᵥ v) -
      (Qᵀ *ᵥ v) ⬝ᵥ (cfc (fun x : ℝ => x ^ s) (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ v))| ≤
        4 * exp (-(d : ℝ) ^ 2 / (2 * s)) * ‖WithLp.toLp 2 v‖ ^ 2 := by
  have h := abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul hA hQ v hK
    ((degree_monomialChebyshevApprox_le s d).trans_lt (by exact_mod_cast hd))
    hspec (fun _ hx => abs_pow_sub_eval_monomialChebyshevApprox_le hs d hx)
  convert h using 1
  ring

/-- **Gauss quadrature error for `exp(−x)`**: for a symmetric `A` with spectrum in `[0, b]` and
`2q` above the approximation degree `exponentialApproxDegree b δ`,
`|vᵀ exp(−A) v − (Qᵀv)ᵀ exp(−QᵀAQ) (Qᵀv)| ≤ 2δ ‖v‖²`.
Source: Sachdeva–Vishnoi (2014) [`sv14`], Thm 4.1; Golub–Meurant (2010) [`gm10`], §6.2.
Atlas: `lanczos-gauss-quadrature` (exponential rate). -/
theorem abs_dotProduct_cfc_exp_neg_mulVec_sub_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (0 : ℝ) b)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (v : n → ℝ) {q : ℕ}
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    (hq : exponentialApproxDegree b δ < 2 * q) :
    |v ⬝ᵥ (cfc (fun x : ℝ => exp (-x)) A *ᵥ v) -
      (Qᵀ *ᵥ v) ⬝ᵥ (cfc (fun x : ℝ => exp (-x)) (Qᵀ * A * Q) *ᵥ (Qᵀ *ᵥ v))| ≤
        2 * δ * ‖WithLp.toLp 2 v‖ ^ 2 :=
  abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul hA hQ v hK
    ((degree_exponentialApprox_le b δ).trans_lt (by exact_mod_cast hq)) hspec
    (fun _ hx => abs_exp_neg_sub_eval_exponentialApprox_le hb hδ hδ1 hx)

/-- **Lanczos-FA error for `exp(−x)`**: for a symmetric `A` with spectrum in `[0, b]` and
`q` above the approximation degree, `‖exp(−A) v − Q exp(−QᵀAQ) Qᵀ v‖² ≤ (2δ)² ‖v‖²`.
Source: Sachdeva–Vishnoi (2014) [`sv14`], Thm 4.1; Saad (1992) [`saad92`], Thm 3.4.
Atlas: `lanczos-fa-error` (exponential rate). -/
theorem dotProduct_cfc_exp_neg_mulVec_sub_krylovFunApprox_self_le {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (0 : ℝ) b)
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (v : n → ℝ) {q : ℕ}
    (hK : krylovSpace A v q ≤ LinearMap.range Q.mulVecLin)
    (hq : exponentialApproxDegree b δ < q) :
    ‖WithLp.toLp 2 (cfc (fun x : ℝ => exp (-x)) A *ᵥ v -
      krylovFunApprox A (fun x : ℝ => exp (-x)) v Q)‖ ^ 2 ≤
        (2 * δ) ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 :=
  dotProduct_cfc_mulVec_sub_krylovFunApprox_self_le hA hQ v hK
    ((degree_exponentialApprox_le b δ).trans_lt (by exact_mod_cast hq)) hspec
    (fun _ hx => abs_exp_neg_sub_eval_exponentialApprox_le hb hδ hδ1 hx)

end NLAlib
