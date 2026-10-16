import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Matrix.Functions.TracePowers

/-! # Hermitian spectral norms below even trace moments

The complex Hermitian spectral theorem compares the named spectral norm with
the unnormalized real trace of any positive even power. Empty matrices are
included when the power is positive.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix
namespace NLAlib
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A complex Hermitian matrix's positive even spectral-norm power is bounded
by the real trace of the same even matrix power. -/
theorem specNorm_pow_two_mul_le_re_trace_pow {A : Matrix d d ℂ}
    (hA : A.IsHermitian) {p : ℕ} (hp : 0 < p) :
    specNorm A ^ (2 * p) ≤ (A ^ (2 * p)).trace.re := by
  cases isEmpty_or_nonempty d with
  | inl hd =>
    have hzero : A = 0 := Subsingleton.elim _ _
    subst A
    simp [specNorm_zero, Nat.ne_of_gt hp]
  | inr hd =>
    rw [hA.specNorm_eq_norm_eigenvalues, re_trace_pow_eq_sum_eigenvalues_pow A hA]
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm hA.eigenvalues).1
    rw [← hi]
    calc
      ‖hA.eigenvalues i‖ ^ (2 * p) = hA.eigenvalues i ^ (2 * p) := by
        rw [Real.norm_eq_abs, ← abs_pow]
        exact abs_of_nonneg ((even_two_mul p).pow_nonneg _)
      _ ≤ ∑ j, hA.eigenvalues j ^ (2 * p) :=
        Finset.single_le_sum (fun j _ => (even_two_mul p).pow_nonneg _)
          (Finset.mem_univ i)

end NLAlib
