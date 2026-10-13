import NLAlib.ForMathlib.Algebra.OrderedNodalWeights
import Mathlib.Order.Fin.InsertNth

/-!
# Signs of the nodal product inside ordered gaps

Insertion of the evaluation point into the ordered grid turns the nodal-product sign into
an already established alternating nodal-weight sign.
Source: the finite node-product formula in the peak-Jacobian certificate.
-/

noncomputable section

open Polynomial Finset Set

namespace NLAlib

/-- The real nodal product has its strict alternating sign in each ordered grid gap.
Source: insertion into the ordered nodal-weight product. -/
theorem signed_eval_nodal_in_gap_pos {n : ℕ} {v : Fin (n + 2) → ℝ}
    (hv : StrictMono v) (i : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (v i.castSucc) (v i.succ)) :
    0 < (-1 : ℝ) ^ (n + 1 - i.val) * (Lagrange.nodal univ v).eval x := by
  let p : Fin (n + 3) := i.castSucc.succ
  let w : Fin (n + 3) → ℝ := Fin.insertNth p x v
  have hw : StrictMono w := Fin.strictMono_insertNth hv i x hx.1 hx.2
  have hweight : Lagrange.nodalWeight univ w p = ((Lagrange.nodal univ v).eval x)⁻¹ := by
    rw [nodalWeight_eq_prod_ite, Fin.prod_univ_succAbove _ p]
    simp only [w, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
      Fin.succAbove_ne, if_false, ite_true, one_mul]
    rw [Lagrange.eval_nodal, prod_inv_distrib]
  have he : n + 2 - p.val = n + 1 - i.val := by dsimp [p]; omega
  have hpos := signed_nodalWeight_pos hw p
  rw [he, hweight] at hpos
  rcases mul_pos_iff.mp hpos with h | h
  · exact mul_pos h.1 (inv_pos.mp h.2)
  · exact mul_pos_of_neg_of_neg h.1 (inv_lt_zero'.mp h.2)

/-- The nodal product does not vanish at an interior point of an ordered node gap.
Source: its strict alternating gap sign. -/
theorem eval_nodal_in_gap_ne_zero {n : ℕ} {v : Fin (n + 2) → ℝ}
    (hv : StrictMono v) (i : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (v i.castSucc) (v i.succ)) :
    (Lagrange.nodal univ v).eval x ≠ 0 := by
  have h := signed_eval_nodal_in_gap_pos hv i hx
  intro hz
  rw [hz, mul_zero] at h
  exact lt_irrefl _ h

/-- The alternating sign of a gap's nodal product is a common sign times `(-1)^i`.
Source: the ordered gap-product sign formula. -/
theorem eval_nodal_gap_eq_sign_mul_abs {n : ℕ} {v : Fin (n + 2) → ℝ}
    (hv : StrictMono v) (i : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (v i.castSucc) (v i.succ)) :
    (Lagrange.nodal univ v).eval x = (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ i.val *
      |(Lagrange.nodal univ v).eval x| := by
  have hpos := signed_eval_nodal_in_gap_pos hv i hx
  have habs : |(Lagrange.nodal univ v).eval x| =
      (-1 : ℝ) ^ (n + 1 - i.val) * (Lagrange.nodal univ v).eval x := by
    simpa only [abs_mul, abs_neg_one_pow, one_mul] using abs_of_pos hpos
  have hsi : ((-1 : ℝ) ^ i.val) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hsg : ((-1 : ℝ) ^ (n + 1 - i.val)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have he : n + 1 = (n + 1 - i.val) + i.val := by omega
  have hpfull : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n + 1 - i.val) * (-1 : ℝ) ^ i.val := by
    simpa only [← he] using (pow_add (-1 : ℝ) (n + 1 - i.val) i.val)
  rw [habs, hpfull]
  symm
  calc
    _ = (((-1 : ℝ) ^ (n + 1 - i.val)) ^ 2 * (((-1 : ℝ) ^ i.val) ^ 2)) *
        (Lagrange.nodal univ v).eval x := by ring
    _ = _ := by rw [hsg, hsi]; ring

end NLAlib
