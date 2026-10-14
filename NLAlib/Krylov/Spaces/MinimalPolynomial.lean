import NLAlib.Krylov.Spaces.Grade
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Vector-relative minimal polynomials

Polynomial division by the first Krylov relation identifies every polynomial
annihilating a vector. The scalar field and finite matrix labels are arbitrary.
Source: Saad (2003), Props. 6.1–6.3; operator derivations, Section 5.
Atlas: `krylov-grade`.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The first dependent Krylov power gives a monic annihilator of degree exactly
the grade, including the constant polynomial one for a zero vector.
Source: operator derivations, Section 5. -/
theorem exists_monic_aeval_mulVec_eq_zero_natDegree_eq_krylovGrade
    (A : Matrix n n K) (b : n → K) :
    ∃ p : K[X], p.Monic ∧ p.natDegree = krylovGrade A b ∧ aeval A p *ᵥ b = 0 := by
  obtain ⟨q, hq, heq⟩ := (mem_krylovSpace_iff A b _ _).mp
    (pow_krylovGrade_mulVec_mem_krylovSpace A b)
  refine ⟨X ^ krylovGrade A b - q, monic_X_pow_sub hq, ?_, ?_⟩
  · have hd : (X ^ krylovGrade A b - q).degree =
        (X ^ krylovGrade A b : K[X]).degree :=
      degree_sub_eq_left_of_degree_lt (by simpa only [degree_X_pow] using hq)
    exact (natDegree_eq_of_degree_eq hd).trans (natDegree_X_pow _)
  · rw [map_sub, Matrix.sub_mulVec, map_pow, aeval_X, heq, sub_self]

/-- The monic polynomial of least degree annihilating `b` through `A`.
It is one when `b=0`, including empty matrices.
Source: Saad (2003), Props. 6.1–6.3.
atlas: krylov-grade (partial) -/
def vectorMinpoly (A : Matrix n n K) (b : n → K) : K[X] :=
  Classical.choose (exists_monic_aeval_mulVec_eq_zero_natDegree_eq_krylovGrade A b)

/-- The vector-relative minimal polynomial is monic.
Source: Saad (2003), Props. 6.1–6.3.
atlas: krylov-grade (partial) -/
theorem vectorMinpoly_monic (A : Matrix n n K) (b : n → K) :
    (vectorMinpoly A b).Monic :=
  (Classical.choose_spec (exists_monic_aeval_mulVec_eq_zero_natDegree_eq_krylovGrade A b)).1

/-- The degree of the vector-relative minimal polynomial is the Krylov grade.
Source: Saad (2003), Props. 6.1–6.3.
atlas: krylov-grade (partial) -/
theorem natDegree_vectorMinpoly (A : Matrix n n K) (b : n → K) :
    (vectorMinpoly A b).natDegree = krylovGrade A b :=
  (Classical.choose_spec (exists_monic_aeval_mulVec_eq_zero_natDegree_eq_krylovGrade A b)).2.1

/-- The vector-relative minimal polynomial annihilates its vector.
Source: Saad (2003), Props. 6.1–6.3.
atlas: krylov-grade (partial) -/
theorem aeval_vectorMinpoly_mulVec (A : Matrix n n K) (b : n → K) :
    aeval A (vectorMinpoly A b) *ᵥ b = 0 :=
  (Classical.choose_spec (exists_monic_aeval_mulVec_eq_zero_natDegree_eq_krylovGrade A b)).2.2

/-- A polynomial annihilates the vector exactly when the vector-relative minimal
polynomial divides it. This is the full annihilator interface, with no nonzero
vector or positive dimension assumption. Source: operator derivations, (S1).
atlas: krylov-grade (partial) -/
theorem aeval_mulVec_eq_zero_iff_vectorMinpoly_dvd
    (A : Matrix n n K) (b : n → K) (p : K[X]) :
    aeval A p *ᵥ b = 0 ↔ vectorMinpoly A b ∣ p := by
  constructor
  · intro hp
    have hr : (p %ₘ vectorMinpoly A b).degree < krylovGrade A b := by
      simpa only [← natDegree_vectorMinpoly A b,
        degree_eq_natDegree (vectorMinpoly_monic A b).ne_zero] using
        degree_modByMonic_lt p (vectorMinpoly_monic A b)
    have hzero : aeval A (p %ₘ vectorMinpoly A b) *ᵥ b = 0 := by
      rw [modByMonic_eq_sub_mul_div, map_sub, map_mul, Matrix.sub_mulVec]
      have hc' := (Commute.all (vectorMinpoly A b) (p /ₘ vectorMinpoly A b)).map (aeval A)
      rw [hc'.eq, ← Matrix.mulVec_mulVec, aeval_vectorMinpoly_mulVec,
        Matrix.mulVec_zero, hp, sub_self]
    exact (modByMonic_eq_zero_iff_dvd (vectorMinpoly_monic A b)).mp
      (eq_zero_of_aeval_mulVec_eq_zero hr hzero)
  · rintro ⟨q, rfl⟩
    have hc := (Commute.all (vectorMinpoly A b) q).map (aeval A)
    rw [map_mul, hc.eq, ← Matrix.mulVec_mulVec, aeval_vectorMinpoly_mulVec,
      Matrix.mulVec_zero]

/-- The vector-relative minimal polynomial divides the operator minimal polynomial.
Source: Saad (2003), Proposition 6.1.
atlas: krylov-grade (partial) -/
theorem vectorMinpoly_dvd_minpoly (A : Matrix n n K) (b : n → K) :
    vectorMinpoly A b ∣ minpoly K A := by
  apply (aeval_mulVec_eq_zero_iff_vectorMinpoly_dvd A b _).mp
  rw [minpoly.aeval, Matrix.zero_mulVec]

/-- A monic grade-degree annihilator is uniquely the vector-relative minimal polynomial.
Source: polynomial division in operator derivations, (S1).
atlas: krylov-grade (partial) -/
theorem eq_vectorMinpoly_of_monic_of_natDegree_eq {A : Matrix n n K} {b : n → K}
    {p : K[X]} (hp : p.Monic) (hdeg : p.natDegree = krylovGrade A b)
    (hzero : aeval A p *ᵥ b = 0) : p = vectorMinpoly A b := by
  apply eq_of_monic_of_dvd_of_natDegree_le (vectorMinpoly_monic A b) hp
    ((aeval_mulVec_eq_zero_iff_vectorMinpoly_dvd A b p).mp hzero)
  rw [hdeg, natDegree_vectorMinpoly]

/-- The operator minimal polynomial has degree at most the finite matrix dimension.
Source: Cayley–Hamilton and polynomial divisibility.
atlas: krylov-grade (partial) -/
theorem natDegree_minpoly_le_card (A : Matrix n n K) :
    (minpoly K A).natDegree ≤ Fintype.card n := by
  simpa only [Matrix.charpoly_natDegree_eq_dim] using
    natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly A) (Matrix.charpoly_monic A).ne_zero

end NLAlib
