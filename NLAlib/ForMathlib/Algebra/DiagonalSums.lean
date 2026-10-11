import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Removing the diagonal of a finite double sum

Source: the finite contraction calculation in operator manuscript
`sh:count-second`; supports `sparse-ose`.
-/

set_option autoImplicit false
open scoped BigOperators
namespace NLAlib

/-- The off-diagonal double sum equals the full double sum minus its diagonal.
Source: finite sum decomposition in manuscript `sh:count-second`;
supports `sparse-ose`. -/
theorem sum_sum_ite_ne_eq_sub_diag {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup R] (f : ι → ι → R) :
    (∑ i, ∑ j, if i = j then 0 else f i j) =
      (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  have hpoint (i j : ι) : (if i = j then 0 else f i j) =
      f i j - if i = j then f i j else 0 := by split_ifs <;> simp
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp

end NLAlib
