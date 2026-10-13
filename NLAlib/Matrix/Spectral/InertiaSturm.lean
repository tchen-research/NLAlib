import NLAlib.Matrix.Spectral.Inertia
import NLAlib.Matrix.Factorizations.SymmetricLU

/-!
# Sturm eigenvalue count from principal minors

The sign-change count follows from symmetric LU as an LDL transpose congruence
and the signs of the finite pivot products. The proof covers all real symmetric
matrices with nonzero shifted leading minors, including zero dimension.
Sources: Golub–Van Loan (2013), Section 8.4.1; Parlett (1998), Chapter 3.
Atlas: `sylvester-inertia`.
-/

noncomputable section
open scoped Matrix
open Matrix
namespace NLAlib

/--
**Eigenvalue count from the leading principal minors (Sturm / Jacobi).** Let `A : Fin m × Fin m`
be real symmetric and `p_k = det (A − xI)_{1:k, 1:k}` (`p_0 = 1`). If every `p_k` (`1 ≤ k ≤ m`)
is nonzero, then the number of eigenvalues of `A` below `x` equals the number of sign changes
in `p_0, p_1, …, p_m`, i.e. `#{k < m : p_k p_{k+1} < 0}`. For an unreduced symmetric
tridiagonal `A` the `p_k` obey the Sturm three-term recurrence
`p_{k+1} = (a_{k+1} − x) p_k − b_k² p_{k−1}`, and this count drives bisection.
Golub–Van Loan (2013) [`gvl13`], Thm 8.5.1 and §8.4.1; Parlett (1998) [`parlett98`], Ch. 3;
Horn–Johnson (2013) [`hj13`], §4.5. Nonzero leading minors give `LU` of `A − xI`
(`luSucceeds_iff_forall_leadingMinor_ne_zero`), symmetric so
`A − xI = L D Lᵀ` with `d_{k+1} = p_{k+1}/p_k` (`IsLU.leadingMinor_eq_prod`); then
`card_eigenvalues_lt_eq_card_neg_of_eq_mul_diagonal_mul` and `p_{k+1}/p_k < 0 ↔ p_k p_{k+1} < 0`.
atlas: sylvester-inertia -/
theorem card_eigenvalues_lt_eq_card_sign_changes {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) {x : ℝ}
    (hp : ∀ k, 1 ≤ k → k ≤ m → leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) k ≠ 0) :
    (Finset.univ.filter fun i => hA.eigenvalues i < x).card =
      (Finset.univ.filter fun k : Fin m =>
        leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) (k : ℕ) *
          leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) ((k : ℕ) + 1) < 0).card := by
  let M := A - x • (1 : Matrix (Fin m) (Fin m) ℝ)
  have hM : M.IsSymm := by
    change Mᵀ = M
    dsimp [M]
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
      (Matrix.isHermitian_iff_isSymm.mp hA).eq]
  have hminor (k : ℕ) (hk : k ≤ m) : leadingMinor M k ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · exact hp k hk0 hk
  have hlu := isLU_lu ((luSucceeds_iff_forall_leadingMinor_ne_zero M).mpr hminor)
  have hL : IsUnit (lu M).1 := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [hlu.isUnitLowerTriangular.det_eq_one]
    exact isUnit_one)
  have hLDL := hlu.eq_mul_diagonal_mul_transpose hM
  have hcount := card_eigenvalues_lt_eq_card_neg_of_eq_mul_diagonal_mul hA hL hLDL
  have hprod (k : ℕ) (hk : k ≤ m) :
      leadingMinor M k = ∏ i : Fin k, (lu M).2 (Fin.castLE hk i) (Fin.castLE hk i) := by
    exact hlu.leadingMinor_eq_prod k hk
  have hpivot (k : Fin m) : leadingMinor M ((k : ℕ) + 1) =
      leadingMinor M (k : ℕ) * (lu M).2 k k := by
    rw [hprod ((k : ℕ) + 1) (by omega), Fin.prod_univ_castSucc,
      hprod (k : ℕ) (by omega)]
    rfl
  rw [hcount]
  congr 1
  apply Finset.filter_congr
  intro k hk
  have hpk : leadingMinor M (k : ℕ) ≠ 0 := hminor k k.isLt.le
  have hsq : 0 < leadingMinor M (k : ℕ) ^ 2 := sq_pos_of_ne_zero hpk
  change (lu M).2 k k < 0 ↔ leadingMinor M (k : ℕ) * leadingMinor M ((k : ℕ) + 1) < 0
  rw [hpivot, show leadingMinor M (k : ℕ) * (leadingMinor M (k : ℕ) * (lu M).2 k k) =
    leadingMinor M (k : ℕ) ^ 2 * (lu M).2 k k by ring]
  simpa only [mul_zero] using (mul_lt_mul_iff_of_pos_left (b := (lu M).2 k k) (c := (0 : ℝ)) hsq).symm

end NLAlib
