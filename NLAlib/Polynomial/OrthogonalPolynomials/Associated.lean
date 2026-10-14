import NLAlib.Polynomial.OrthogonalPolynomials.SecondKind

/-! # Associated monic recurrence polynomials

Shifting a finite three-term recurrence gives its associated monic sequence.
The actual second-kind numerator is the first associated sequence multiplied
by the original mass. Source: Gautschi (2004), Chapter 1, AQ17.
-/

noncomputable section
open Polynomial
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- The monic polynomial sequence with the given recurrence coefficients
shifted by `s`. The definition does not involve nested rational divisions. -/
def associatedMonicPolynomial (α β : ℕ → 𝕜) (s : ℕ) : ℕ → 𝕜[X]
  | 0 => 1
  | 1 => X-C (α s)
  | n+2 => (X-C (α (s+n+1))) * associatedMonicPolynomial α β s (n+1) -
      C (β (s+n+1)) * associatedMonicPolynomial α β s n

/-- Associated order zero is the constant one. -/
@[simp] theorem associatedMonicPolynomial_zero (α β : ℕ → 𝕜) (s : ℕ) :
    associatedMonicPolynomial α β s 0 = 1 := rfl

/-- Associated order one uses the diagonal coefficient at the shifted start. -/
@[simp] theorem associatedMonicPolynomial_one (α β : ℕ → 𝕜) (s : ℕ) :
    associatedMonicPolynomial α β s 1 = X-C (α s) := rfl

/-- Associated polynomials obey the original recurrence with every coefficient
shifted by the same amount. Source: Gautschi (2004), Chapter 1, AQ17.
atlas: jacobi-fraction-second-kind (partial) -/
theorem associatedMonicPolynomial_add_two (α β : ℕ → 𝕜) (s n : ℕ) :
    associatedMonicPolynomial α β s (n+2) =
      (X-C (α (s+n+1))) * associatedMonicPolynomial α β s (n+1) -
        C (β (s+n+1)) * associatedMonicPolynomial α β s n := rfl

/-- Every associated polynomial is monic and has exactly its order as degree,
regardless of signs or vanishing recurrence coefficients.
atlas: jacobi-fraction-second-kind (partial) -/
theorem monic_and_natDegree_associatedMonicPolynomial (α β : ℕ → 𝕜) (s n : ℕ) :
    (associatedMonicPolynomial α β s n).Monic ∧
      (associatedMonicPolynomial α β s n).natDegree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => exact ⟨monic_X_sub_C _, natDegree_X_sub_C _⟩
  | more n ih ih1 =>
    rw [associatedMonicPolynomial_add_two]
    have hleft : ((X-C (α (s+n+1))) * associatedMonicPolynomial α β s (n+1)).Monic :=
      (monic_X_sub_C _).mul ih1.1
    have hdeg : ((X-C (α (s+n+1))) * associatedMonicPolynomial α β s (n+1)).degree =
        ((n+2 : ℕ) : WithBot ℕ) := by
      rw [degree_mul, degree_X_sub_C, degree_eq_natDegree ih1.1.ne_zero, ih1.2]
      norm_cast
      omega
    have hsmall : (C (β (s+n+1)) * associatedMonicPolynomial α β s n).degree <
        ((X-C (α (s+n+1))) * associatedMonicPolynomial α β s (n+1)).degree := by
      rw [hdeg, C_mul']
      apply (degree_smul_le _ _).trans_lt
      rw [degree_eq_natDegree ih.1.ne_zero, ih.2]
      exact_mod_cast (show n < n+2 by omega)
    have hmonic := hleft.sub_of_left hsmall
    refine ⟨hmonic, ?_⟩
    have hd := (degree_sub_eq_left_of_degree_lt hsmall).trans hdeg
    rw [degree_eq_natDegree hmonic.ne_zero] at hd
    exact WithBot.coe_inj.mp hd

/-- The actual second-kind numerator is original mass times the first
associated monic sequence, including mass zero as a total algebraic identity.
Source: Gautschi (2004), Chapter 1, AQ17.
atlas: jacobi-fraction-second-kind (partial) -/
theorem secondKindPolynomial_eq_mass_mul_associatedMonicPolynomial
    (L : 𝕜[X] →ₗ[𝕜] 𝕜) (n : ℕ) :
    secondKindPolynomial L (n+1) = C (L 1) *
      associatedMonicPolynomial (orthogonalRecurrenceAlpha L) (orthogonalRecurrenceBeta L) 1 n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [secondKindPolynomial, associatedMonicPolynomial]; ring
  | more n ih ih1 =>
    rw [show n+2+1 = (n+1)+2 by omega, secondKindPolynomial_add_two,
      ih1, ih, associatedMonicPolynomial_add_two]
    have heq : 1+n+1 = n+1+1 := by omega
    rw [heq]
    ring

end NLAlib
