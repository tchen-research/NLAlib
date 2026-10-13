import NLAlib.Matrix.Spectral.Inertia

/-!
# Experimental Sturm eigenvalue count from principal minors

The unfinished Sturm/Jacobi sign-change count is isolated from the proved inertia API.
The latter supports deterministic matrix-function inequalities through definite-pair
congruence and must not import this scaffold.
Sources: Golub–Van Loan (2013), Section 8.4.1; Parlett (1998), Chapter 3.
Atlas: `sylvester-inertia`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- SCAFFOLD: sylvester-inertia
**Eigenvalue count from the leading principal minors (Sturm / Jacobi).** Let `A : Fin m × Fin m`
be real symmetric and `p_k = det (A − xI)_{1:k, 1:k}` (`p_0 = 1`). If every `p_k` (`1 ≤ k ≤ m`)
is nonzero, then the number of eigenvalues of `A` below `x` equals the number of sign changes
in `p_0, p_1, …, p_m`, i.e. `#{k < m : p_k p_{k+1} < 0}`. For an unreduced symmetric
tridiagonal `A` the `p_k` obey the Sturm three-term recurrence
`p_{k+1} = (a_{k+1} − x) p_k − b_k² p_{k−1}`, and this count drives bisection.
Golub–Van Loan (2013) [`gvl13`], Thm 8.5.1 and §8.4.1; Parlett (1998) [`parlett98`], Ch. 3;
Horn–Johnson (2013) [`hj13`], §4.5. Proof sketch: nonzero leading minors give `LU` of `A − xI`
(`luSucceeds_iff_forall_det_ne_zero`, D-A's `Matrix/Factorizations/LU.lean`), symmetric so
`A − xI = L D Lᵀ` with `d_{k+1} = p_{k+1}/p_k` (`IsLU.det_leadingSubmatrix`); then
`card_eigenvalues_lt_eq_card_neg_of_eq_mul_diagonal_mul` and `p_{k+1}/p_k < 0 ↔ p_k p_{k+1} < 0`.
Difficulty 3.
atlas: sylvester-inertia -/
theorem card_eigenvalues_lt_eq_card_sign_changes {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) {x : ℝ}
    (hp : ∀ k, 1 ≤ k → k ≤ m → leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) k ≠ 0) :
    (Finset.univ.filter fun i => hA.eigenvalues i < x).card =
      (Finset.univ.filter fun k : Fin m =>
        leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) (k : ℕ) *
          leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) ((k : ℕ) + 1) < 0).card := by
  sorry


end NLAlib
