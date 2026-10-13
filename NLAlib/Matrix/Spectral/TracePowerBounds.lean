/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import NLAlib.Matrix.Spectral.TraceEigenvalues
import NLAlib.Matrix.Spectral.QuadraticProbe
/-!
# Even trace powers of real symmetric matrices

For a real symmetric matrix `A`, the trace of an even power is the power sum of the eigenvalues,
so it is nonnegative and dominates the same power of the spectral norm:

* `trace_pow_nonneg_of_even`: `0 ≤ tr (Aⁿ)` for even `n`;
* `specNorm_pow_two_mul_le_trace_pow`: `‖A‖₂ ^ (2q) ≤ tr (A ^ (2q))` for `q > 0`.

The second is the deterministic step of the trace-moment method (Markov's inequality on
`E tr A^{2q}`).
Source: ported from `SparseFockFormal.MatrixTail` (`trace_even_pow_nonneg`,
`opNorm_even_pow_le_trace`), commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b;
supports `sparse-ose`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every even power of a real symmetric matrix has nonnegative trace.

Source: ported from `SparseFockFormal.MatrixTail.trace_even_pow_nonneg`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem trace_pow_nonneg_of_even {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {n : ℕ}
    (hn : Even n) : 0 ≤ (A ^ n).trace := by
  rw [trace_pow_eq_sum_eigenvalues hA]
  exact Finset.sum_nonneg fun i _hi => hn.pow_nonneg (hA.eigenvalues i)

/-- An even power of the spectral norm of a real symmetric matrix is bounded by the trace of the
same matrix power. The hypothesis `0 < q` covers the empty index type, where both sides vanish.

Source: ported from `SparseFockFormal.MatrixTail.opNorm_even_pow_le_trace` (and its
`_of_nonempty` variant), b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`. -/
theorem specNorm_pow_two_mul_le_trace_pow {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {q : ℕ}
    (hq : 0 < q) : specNorm A ^ (2 * q) ≤ (A ^ (2 * q)).trace := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      have hzero : A = 0 := Subsingleton.elim _ _
      subst A
      simp [specNorm_eq_norm, Nat.ne_of_gt hq]
  | inr hι =>
      rw [specNorm_eq_norm_eigenvalues hA, trace_pow_eq_sum_eigenvalues hA]
      obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hA.eigenvalues).1
      rw [← hi]
      calc
        ‖hA.eigenvalues i‖ ^ (2 * q) = hA.eigenvalues i ^ (2 * q) := by
          rw [Real.norm_eq_abs, ← abs_pow]
          exact abs_of_nonneg ((even_two_mul q).pow_nonneg (hA.eigenvalues i))
        _ ≤ ∑ j, hA.eigenvalues j ^ (2 * q) :=
          Finset.single_le_sum
            (fun j _hj => (even_two_mul q).pow_nonneg (hA.eigenvalues j))
            (Finset.mem_univ i)

end NLAlib
