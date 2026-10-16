import Mathlib.Tactic.Ring

/-!
# Cayley squaring for Newton iteration in a commutative ring

These identities only assume the two displayed inverse equations. They
can therefore be used inside a matrix bicommutant, even with zero divisors.
Higham, Functions of Matrices, matrix-sign Newton iteration.
-/

namespace CommRing
variable {R : Type*} [CommRing R]

/-- The denominator after Cayley squaring is the product of the two
original denominators. -/
theorem one_sub_sq_mul_inverse_product (t d e : R)
    (hd : (1-t)*d=1) (he : (1+t)*e=1) : (1-t^2)*(d*e)=1 := by
  calc
    _ = ((1-t)*d)*((1+t)*e) := by ring
    _ = 1 := by rw [hd, he, one_mul]

/-- The inverse of the inverse-Cayley value swaps the two factors. -/
theorem cayley_value_mul_inverse (t d e : R)
    (hd : (1-t)*d=1) (he : (1+t)*e=1) : (d*(1+t))*(e*(1-t))=1 := by
  calc
    _ = ((1-t)*d)*((1+t)*e) := by ring
    _ = 1 := by rw [hd, he, one_mul]

/-- Newton averaging of a Cayley value and its inverse squares the
Cayley coordinate. -/
theorem half_mul_cayley_add_inverse (t d e c : R)
    (hd : (1-t)*d=1) (he : (1+t)*e=1) (hc : c*2=1) :
    c*(d*(1+t)+e*(1-t)) = (d*e)*(1+t^2) := by
  calc
    _ = c*((d*(1+t))*(e*(1+t))+(e*(1-t))*(d*(1-t))) := by
      rw [mul_comm e (1+t), he, mul_comm d (1-t), hd, mul_one, mul_one]
    _ = c*(d*e)*((1+t)^2+(1-t)^2) := by ring
    _ = (c*2)*(d*e)*(1+t^2) := by ring
    _ = _ := by rw [hc, one_mul]

end CommRing

namespace CommRing
variable {R : Type*} [CommRing R]

/-- Undoing a Cayley transform only uses its denominator's inverse equation. -/
theorem one_sub_cayley_mul (x e : R) (he : (x+1)*e=1) :
    (1-(x-1)*e)*x = 1+(x-1)*e := by
  calc
    _ = 1+(x-1)*e+(x-1)*(1-(x+1)*e) := by ring
    _ = _ := by rw [he, sub_self, mul_zero, add_zero]

end CommRing
