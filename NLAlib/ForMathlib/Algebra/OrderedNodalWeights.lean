import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Signs of nodal weights on an ordered real grid

Source: the product formula for Lagrange nodal weights.
-/

noncomputable section

open Finset

namespace NLAlib

/-- Reinsert a neutral diagonal term into the finite nodal-weight product.
Source: the Lagrange product formula. -/
theorem nodalWeight_eq_prod_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (i : ι) :
    Lagrange.nodalWeight univ v i = ∏ j, if j = i then 1 else (v i - v j)⁻¹ := by
  unfold Lagrange.nodalWeight
  symm
  calc
    _ = (if i = i then (1 : ℝ) else (v i - v i)⁻¹) *
        ∏ j ∈ univ.erase i, if j = i then 1 else (v i - v j)⁻¹ :=
      (mul_prod_erase univ (fun j => if j = i then (1 : ℝ) else (v i - v j)⁻¹) (mem_univ i)).symm
    _ = _ := by
      rw [if_pos rfl, one_mul]
      exact prod_congr rfl fun j hj => if_neg (mem_erase.mp hj).1

/-- The nodal weights of an increasing `(n+1)`-node real grid have alternating signs.
Source: the signs of the factors in the finite Lagrange product. -/
theorem signed_nodalWeight_pos {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : StrictMono v)
    (i : Fin (n + 1)) : 0 < (-1 : ℝ) ^ (n - i.val) * Lagrange.nodalWeight univ v i := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simp [Lagrange.nodalWeight]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [nodalWeight_eq_prod_ite, Fin.prod_univ_succ]
      simp only [Fin.val_zero, Nat.sub_zero, ite_true, one_mul, Fin.succ_ne_zero, ite_false]
      have heq : (-1 : ℝ) ^ (n + 1) * ∏ j : Fin (n + 1), (v 0 - v j.succ)⁻¹ =
          ∏ j : Fin (n + 1), -(v 0 - v j.succ)⁻¹ := by
        simpa only [card_univ, Fintype.card_fin] using
          (prod_neg (s := univ) (fun j : Fin (n + 1) => (v 0 - v j.succ)⁻¹)).symm
      rw [heq]
      apply prod_pos
      intro j hj
      have h := hv (show (0 : Fin (n + 2)) < j.succ by exact Fin.succ_pos j)
      exact neg_pos.mpr (inv_lt_zero'.mpr (sub_neg.mpr h))
    · have hw : StrictMono (fun k : Fin (n + 1) => v k.succ) := hv.comp Fin.strictMono_succ
      have hold := ih hw j
      have hfirst : 0 < (v j.succ - v 0)⁻¹ := inv_pos.mpr (sub_pos.mpr
        (hv (show (0 : Fin (n + 2)) < j.succ by exact Fin.succ_pos j)))
      rw [nodalWeight_eq_prod_ite, Fin.prod_univ_succ]
      rw [if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simp only [Fin.val_succ, Nat.add_sub_add_right, Fin.succ_inj]
      rw [← nodalWeight_eq_prod_ite (fun k : Fin (n + 1) => v k.succ) j]
      have hprod := mul_pos hfirst hold
      simpa only [mul_left_comm, mul_assoc] using hprod



/-- Low-degree polynomial evaluations have vanishing top barycentric coefficient.
Source: the top coefficient in the exact Lagrange interpolation formula. -/
theorem sum_eval_mul_nodalWeight_eq_zero {n : ℕ} {v : Fin (n + 1) → ℝ}
    (hv : Function.Injective v) {p : Polynomial ℝ} (hp : p.degree < n) :
    (∑ i, p.eval (v i) * Lagrange.nodalWeight univ v i) = 0 := by
  have hcoeff := Lagrange.coeff_eq_sum (s := univ) hv.injOn
    (hp.trans_le (by simp only [card_univ, Fintype.card_fin]; exact_mod_cast Nat.le_succ n))
  have hz := Polynomial.coeff_eq_zero_of_degree_lt hp
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, hz] at hcoeff
  simpa only [Lagrange.nodalWeight, Finset.prod_inv_distrib, div_eq_mul_inv] using hcoeff.symm

/-- Alternating absolute nodal weights are the signed barycentric weights.
Source: the alternating sign of an ordered grid's nodal weights. -/
theorem neg_one_pow_mul_abs_nodalWeight {n : ℕ} {v : Fin (n + 1) → ℝ}
    (hv : StrictMono v) (r : Fin (n + 1)) (i : ℕ) :
    (-1 : ℝ) ^ (r.val + i) * |Lagrange.nodalWeight univ v r| =
      (-1 : ℝ) ^ (n + i) * Lagrange.nodalWeight univ v r := by
  have hpos := signed_nodalWeight_pos hv r
  have habs : |Lagrange.nodalWeight univ v r| =
      (-1 : ℝ) ^ (n - r.val) * Lagrange.nodalWeight univ v r := by
    simpa only [abs_mul, abs_neg_one_pow, one_mul] using abs_of_pos hpos
  rw [habs, ← mul_assoc, ← pow_add, show (r.val + i) + (n - r.val) = n + i by omega]

end NLAlib
