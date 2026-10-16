import NLAlib.Polynomial.BestApproximation.PolarTaylor
import NLAlib.Polynomial.BestApproximation.OddMinimax

/-! # Coefficient realization and rescaling of the finite polar competitor

The finite inverse-square-root competitor belongs to the actual admissible
odd coefficient space. Rescaling gives its positive lower envelope on any
positive interval, so it may be compared to a genuine minimax update.
Source: Polar Express, §3 and Appendix D; matrix-toolkit re-derivation §40.
-/
noncomputable section
open Polynomial Finset Set
namespace NLAlib

/-- The finite Taylor competitor as a degree-`q` polynomial in the squared input. -/
def polarTaylorCoefficientPolynomial (q : ℕ) : ℝ[X] :=
  ∑ j ∈ range (q + 1), C (polarTaylorCoeff j) * (1 - X) ^ j

/-- Its degree bound is finite and applies also to `q=0`. -/
theorem natDegree_polarTaylorCoefficientPolynomial_le (q : ℕ) :
    (polarTaylorCoefficientPolynomial q).natDegree ≤ q := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjq : j ≤ q := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_pow_le.trans
  have hd : (1 - X : ℝ[X]).natDegree ≤ 1 := by
    simpa using (Polynomial.natDegree_sub_le (1 : ℝ[X]) X)
  exact (Nat.mul_le_mul_left j hd).trans (by simpa using hjq)

/-- The ordinary coefficients realize the Taylor competitor in exactly the
same coefficient model used by the minimax problem and the matrix algorithm. -/
theorem oddScalarUpdate_polarTaylor_coeff (q : ℕ) (x : ℝ) :
    oddScalarUpdate q (polarTaylorCoefficientPolynomial q).coeff x = polarTaylorUpdate q x := by
  have he := Polynomial.eval_eq_sum_range'
    (p := polarTaylorCoefficientPolynomial q)
    (Nat.lt_succ_of_le (natDegree_polarTaylorCoefficientPolynomial_le q)) (x ^ 2)
  have heval : (polarTaylorCoefficientPolynomial q).eval (x ^ 2) =
      polarTaylorSum q (1 - x ^ 2) := by
    simp [polarTaylorCoefficientPolynomial, polarTaylorSum, Polynomial.eval_finsetSum]
  rw [heval] at he
  rw [polarTaylorUpdate, he, Finset.mul_sum, oddScalarUpdate]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add, pow_one, pow_mul]
  ring

/-- The finite Taylor competitor is an actual member of the allowed odd
polynomial coefficient class. -/
theorem exists_oddScalarUpdate_eq_polarTaylorUpdate (q : ℕ) :
    ∃ c : ℕ → ℝ, ∀ x, oddScalarUpdate q c x = polarTaylorUpdate q x :=
  ⟨(polarTaylorCoefficientPolynomial q).coeff, oddScalarUpdate_polarTaylor_coeff q⟩

/-- A genuine admissible odd coefficient competitor with the exact squared-gap
lower envelope on an arbitrary positive interval.
Source: Polar Express, Appendix D, finite Taylor competitor route.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem exists_oddScalarUpdate_interval_competitor (q : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℕ → ℝ, ∀ x ∈ Icc a b,
      Real.sqrt (1 - (1 - (a / b) ^ 2) ^ (q + 1)) ≤ oddScalarUpdate q c x ∧
        oddScalarUpdate q c x ≤ 1 := by
  have hb : 0 < b := ha.trans_le hab
  let d := (polarTaylorCoefficientPolynomial q).coeff
  refine ⟨fun j => d j / b ^ (2 * j + 1), fun x hx => ?_⟩
  have hx0 : 0 < x / b := div_pos (ha.trans_le hx.1) hb
  have hx1 : x / b ≤ 1 := (div_le_one hb).mpr hx.2
  have hp := polarTaylorUpdate_pos_le_one q hx0 hx1
  have ha0 : 0 ≤ a / b := (div_pos ha hb).le
  have halx : a / b ≤ x / b := (div_le_div_iff_of_pos_right hb).mpr hx.1
  have hg : 0 ≤ 1 - (x / b) ^ 2 := by nlinarith
  have hgap : 1 - (x / b) ^ 2 ≤ 1 - (a / b) ^ 2 := by nlinarith
  have hsq := one_sub_pow_le_polarTaylorUpdate_sq q ⟨hx0.le, hx1⟩
  have hpow := pow_le_pow_left₀ hg hgap (q + 1)
  have hlower : 1 - (1 - (a / b) ^ 2) ^ (q + 1) ≤ polarTaylorUpdate q (x / b) ^ 2 := by
    linarith
  have hsqrt : Real.sqrt (1 - (1 - (a / b) ^ 2) ^ (q + 1)) ≤
      polarTaylorUpdate q (x / b) := (Real.sqrt_le_left hp.1.le).mpr hlower
  have he : oddScalarUpdate q (fun j => d j / b ^ (2 * j + 1)) x =
      polarTaylorUpdate q (x / b) := by
    simpa only [one_mul, oddScalarUpdate_polarTaylor_coeff, d] using
      oddScalarUpdate_rescale q d 1 b x
  rw [he]
  exact ⟨hsqrt, hp.2⟩

end NLAlib
